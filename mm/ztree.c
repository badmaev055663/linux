// SPDX-License-Identifier: GPL-2.0-only
/*
 * ztree.c
 *
 * Author: Ananda Badmaev <a.badmaev@clicknet.pro>
 * Copyright (C) 2021, Konsulko AB.
 *
 * This implementation is based on z3fold written by Vitaly Wool.
 * Ztree is a small object allocator with the intention to serve as a
 * zpool backend. It operates on page blocks and stores integer number
 * of compressed pages per block which results in determinism and
 * simplicity. Red-black trees are used for efficient block organization.
 *
 * ztree doesn't export any API and is meant to be used via zpool API.
 */

#define pr_fmt(fmt) KBUILD_MODNAME ": " fmt

#include <linux/atomic.h>
#include <linux/mm.h>
#include <linux/module.h>
#include <linux/preempt.h>
#include <linux/slab.h>
#include <linux/spinlock.h>
#include <linux/zpool.h>
#include <linux/rbtree.h>

#define SLOT_FREE 0
#define SLOT_OCCUPIED 1
#define SLOT_MAPPED 2
#define SLOT_UNMAPPED 3

#define SLOT_BITS 4
#define MAX_SLOTS (1 << SLOT_BITS)
#define SLOT_MASK ((0x1UL << SLOT_BITS) - 1)

#define BLOCK_DATA_SIZE(order) ((PAGE_SIZE << order) - sizeof(struct ztree_block))
#define SLOT_SIZE(nslots, order) (round_down((BLOCK_DATA_SIZE(order) / nslots), sizeof(long)))

struct ztree_pool;

struct ztree_ops {
	int (*evict)(struct ztree_pool *pool, unsigned long handle);
};

/**
 * struct ztree_block - block metadata
 * Block consists of several (1/2/4/8) pages and contains fixed
 * integer number of slots for allocating compressed pages.
 *
 * block_node:		 links block into the relevant tree in the pool
 * slot_info:	     contains data about free/occupied slots
 * block_index:	     unique for each ztree_block in the tree
 * free_slots:		 number of free slots in the block
 * coeff:            to switch between blocks
 * under_reclaim:    if true shows that block is being evicted
 */
struct ztree_block {
	spinlock_t lock;
	struct rb_node block_node;
	u8 slot_info[MAX_SLOTS];
	unsigned long block_index;
	unsigned short free_slots;
	unsigned short coeff;
	bool under_reclaim;
};

/**
 * struct tree_desc - general metadata for block trees
 * Each block tree stores only blocks of corresponding type which means
 * that all blocks in it have the same number and size of slots.
 * All slots are aligned to size of long.
 *
 * slot_size:		size of slot for this tree
 * slots_per_block:	number of slots per block for this tree
 * order:			order for __get_free_pages
 */
static const struct tree_desc {
	const unsigned int slot_size;
	const unsigned short slots_per_block;
	const unsigned short order;
} tree_desc[] = {
	{ SLOT_SIZE(16, 0), 16, 0 },
	{ SLOT_SIZE(12, 0), 12, 0 },
	{ SLOT_SIZE(9, 0), 9, 0 },
	{ SLOT_SIZE(14, 1), 14, 1 },
	{ SLOT_SIZE(12, 1), 12, 1 },
	{ SLOT_SIZE(10, 1), 10, 1 },
	{ SLOT_SIZE(8, 1), 8, 1 },
	{ SLOT_SIZE(14, 2), 14, 2 },
	{ SLOT_SIZE(12, 2), 12, 2 },
	{ SLOT_SIZE(10, 2), 10, 2 },
	{ SLOT_SIZE(9, 2), 9, 2 },
	{ SLOT_SIZE(8, 2), 8, 2 },
	{ SLOT_SIZE(14, 3), 14, 3 },
	{ SLOT_SIZE(13, 3), 13, 3 },
	{ SLOT_SIZE(12, 3), 12, 3 },
	{ SLOT_SIZE(11, 3), 11, 3 },
	{ SLOT_SIZE(10, 3), 10, 3 },
	{ SLOT_SIZE(9, 3), 9, 3 },
	{ SLOT_SIZE(7, 3), 7, 3 }
};

/**
 * struct block_tree - stores metadata of particular tree
 * lock:			protects tree
 * root:			root of this tree
 * last_block:		pointer to the last added block in the tree
 * current_block:	pointer to current block for allocation
 * counter:			counter for block_index in ztree_block
 * block_count:		total number of blocks in the tree
 */
struct block_tree {
	spinlock_t lock;
	struct rb_root root;
	struct ztree_block *last_block;
	struct ztree_block *current_block;
	unsigned long counter;
	unsigned int block_count;
};

/**
 * struct ztree_pool - stores metadata for each ztree pool
 * @block_trees:	array of block trees
 * @ops:			pointer to a structure of user defined operations specified at
 *					pool creation time.
 * @alloc_flag:		protects block allocation from memory leak
 *
 * This structure is allocated at pool creation time and maintains metadata
 * for a particular ztree pool.
 */
struct ztree_pool {
	struct block_tree *block_trees;
	const struct ztree_ops *ops;
	struct zpool *zpool;
	const struct zpool_ops *zpool_ops;
	atomic_t alloc_flag;
};

/*****************
 * Helpers
 *****************/

/* compare 2 nodes by block index, used by rb_add() */
static bool node_comp(struct rb_node *node1, const struct rb_node *node2)
{
	struct ztree_block *block1, *block2;

	block1 = rb_entry(node1, struct ztree_block, block_node);
	block2 = rb_entry(node2, struct ztree_block, block_node);
	return block1->block_index < block2->block_index;
}

/*
 * allocate new block and add it to corresponding block tree
 */
static struct ztree_block *alloc_block(struct ztree_pool *pool,
									int block_type, gfp_t gfp)
{
	struct ztree_block *block;
	struct block_tree *tree;

	block = (void *)__get_free_pages(gfp, tree_desc[block_type].order);
	if (!block)
		return NULL;

	tree = &(pool->block_trees)[block_type];

	/* init block data  */
	spin_lock_init(&block->lock);
	memset(block->slot_info, SLOT_FREE, tree_desc[block_type].slots_per_block);
	block->free_slots = tree_desc[block_type].slots_per_block;
	block->coeff = 0;
	block->under_reclaim = false;

	spin_lock(&tree->lock);
	/* block indexation and inserting block into tree */
	block->block_index = tree->counter++;
	rb_add(&block->block_node, &tree->root, node_comp);
	tree->last_block = block;
	tree->block_count++;
	spin_unlock(&tree->lock);
	return block;
}

/*
 * Encodes the handle of a particular slot in the pool using metadata
 */
static inline unsigned long metadata_to_handle(struct ztree_block *block,
							unsigned int block_type, unsigned int slot)
{
	return (unsigned long)(block) + (block_type << SLOT_BITS) + slot;
}

/* Returns block, block type and slot in the pool corresponding to handle */
static inline struct ztree_block *handle_to_metadata(unsigned long handle,
						unsigned int *block_type, unsigned int *slot)
{
	*block_type = (handle & (PAGE_SIZE - 1)) >> SLOT_BITS;
	*slot = handle & SLOT_MASK;
	return (struct ztree_block *)(handle & PAGE_MASK);
}


/*****************
 * API Functions
 *****************/
/**
 * ztree_create_pool() - create a new ztree pool array
 * @gfp:	gfp flags when allocating the ztree pool structure
 * @ops:	user-defined operations for the ztree pool
 *
 * Return: pointer to the new ztree pool or NULL if the metadata allocation
 * failed.
 */
static struct ztree_pool *ztree_create_pool(gfp_t gfp, const struct ztree_ops *ops)
{
	struct ztree_pool *pool;
	struct block_tree *tree;
	int i, block_types_nr;

	pool = kmalloc(sizeof(struct ztree_pool), gfp);
	if (!pool)
		return NULL;

	block_types_nr = ARRAY_SIZE(tree_desc);

	pool->block_trees = kmalloc_array(block_types_nr, sizeof(struct block_tree), gfp);
	if (!pool->block_trees) {
		kfree(pool);
		return NULL;
	}

	/* init each basic block tree */
	for (i = 0; i < block_types_nr; i++) {
		tree = &(pool->block_trees)[i];
		spin_lock_init(&tree->lock);
		tree->root = RB_ROOT;
		tree->last_block = NULL;
		tree->current_block = NULL;
		tree->counter = 0;
		tree->block_count = 0;
	}
	pool->ops = ops;
	atomic_set(&pool->alloc_flag, 0);
	return pool;
}

/**
 * ztree_destroy_pool() - destroys an existing ztree pool
 * @pool:	the ztree pool to be destroyed
 *
 */
static void ztree_destroy_pool(struct ztree_pool *pool)
{
	kfree(pool->block_trees);
	kfree(pool);
}


/**
 * ztree_alloc() - allocates a slot of appropriate size
 * @pool:	ztree pool from which to allocate
 * @size:	size in bytes of the desired allocation
 * @gfp:	gfp flags used if the pool needs to grow
 * @handle:	handle of the new allocation
 *
 * Return: 0 if success and handle is set, otherwise -EINVAL if the size or
 * gfp arguments are invalid or -ENOMEM if the pool was unable to allocate
 * a new slot.
 */
static int ztree_alloc(struct ztree_pool *pool, size_t size, gfp_t gfp,
			unsigned long *handle)
{
	unsigned int block_type, slot;
	struct ztree_block *block;
	struct block_tree *tree;

	if (!size)
		return -EINVAL;

	if (size > PAGE_SIZE)
		return -ENOSPC;

	/* find basic block type with suitable slot size */
	for (block_type = 0; block_type < ARRAY_SIZE(tree_desc); block_type++) {
		if (size <= tree_desc[block_type].slot_size)
			break;
	}
	tree = &(pool->block_trees[block_type]);

check:
	spin_lock(&tree->lock);
	/* check if there are free slots in the current and the last added blocks */
	if (tree->current_block && tree->current_block->free_slots > 0) {
		block = tree->current_block;
		goto found;
	}
	if (tree->last_block && tree->last_block->free_slots > 0) {
		block = tree->last_block;
		goto found;
	}
	spin_unlock(&tree->lock);

	/* not found block with free slots try to allocate new empty block */
	if (atomic_cmpxchg(&pool->alloc_flag, 0, 1))
		goto check;
	block = alloc_block(pool, block_type, gfp & ~(__GFP_HIGHMEM | __GFP_MOVABLE));
	if (block) {
		spin_lock(&tree->lock);
		tree->current_block = block;
		goto found;
	}
	atomic_set(&pool->alloc_flag, 0);
	return -ENOMEM;

found:
	spin_lock(&block->lock);
	block->free_slots--;
	spin_unlock(&tree->lock);
	/* find the first free slot in block */
	for (slot = 0; slot < tree_desc[block_type].slots_per_block; slot++) {
		if (block->slot_info[slot] == SLOT_FREE)
			break;
	}
	block->slot_info[slot] = SLOT_OCCUPIED;
	block->coeff = block->free_slots *
			(tree_desc[block_type].slots_per_block - block->free_slots);
	spin_unlock(&block->lock);
	*handle = metadata_to_handle(block, block_type, slot);
	atomic_set(&pool->alloc_flag, 0);
	return 0;
}

/**
 * ztree_free() - frees the allocation associated with the given handle
 * @pool:	pool in which the allocation resided
 * @handle:	handle associated with the allocation returned by ztree_alloc()
 *
 */
static void ztree_free(struct ztree_pool *pool, unsigned long handle)
{
	unsigned int slot, block_type;
	struct ztree_block *block;
	struct block_tree *tree;

	block = handle_to_metadata(handle, &block_type, &slot);
	tree = &(pool->block_trees[block_type]);

	if (block->under_reclaim)
		return;
	spin_lock(&tree->lock);
	block->free_slots++;
	/* if all slots in block are empty delete whole block */
	if (block->free_slots == tree_desc[block_type].slots_per_block) {
		rb_erase(&block->block_node, &tree->root);
		tree->block_count--;

		/* if the last block to be deleted */
		if (block == tree->last_block) {
			tree->current_block = NULL;
			tree->last_block = NULL;
		/* otherwise set current block to last block */
		} else {
			tree->current_block = tree->last_block;
		}
		spin_unlock(&tree->lock);
		free_pages((unsigned long)block, tree_desc[block_type].order);
		return;
	}
	/* switch current block */
	if (!tree->current_block || block->coeff >= tree->current_block->coeff)
		tree->current_block = block;
	spin_lock(&block->lock);
	spin_unlock(&tree->lock);
	block->slot_info[slot] = SLOT_FREE;
	block->coeff = block->free_slots *
				(tree_desc[block_type].slots_per_block - block->free_slots);
	spin_unlock(&block->lock);
}

/**
 * ztree_reclaim_block() - evicts allocations from block and frees it
 * @pool:	pool from which a block will attempt to be evicted
 *
 * Returns: pages reclaimed count if block is successfully freed
 *          otherwise -EINVAL if there are no blocks to evict
 */
static int ztree_reclaim_block(struct ztree_pool *pool)
{
	struct ztree_block *block;
	struct rb_node *tmp;
	struct block_tree *tree;
	unsigned long handle, block_type, slot;
	int ret, reclaimed;

	/* start with tree storing blocks with the worst compression and try
	 * to evict block with the lowest index (the first element in tree)
	 */
	for (block_type = ARRAY_SIZE(tree_desc) - 1; block_type >= 0; --block_type) {
		tree = &(pool->block_trees[block_type]);
		spin_lock(&tree->lock);

		/* find the first block in tree */
		tmp = rb_first(&tree->root);

		if (tmp == NULL) {
			spin_unlock(&tree->lock);
			continue;
		}
		block = rb_entry(tmp, struct ztree_block, block_node);

		/* skip iteration if this block is current or last */
		if (block == tree->current_block || block == tree->last_block) {
			spin_unlock(&tree->lock);
			continue;
		}
		block->under_reclaim = true;
		spin_unlock(&tree->lock);
		reclaimed = 0;

		/* try to evict all UNMAPPED slots in block */
		for (slot = 0; slot < tree_desc[block_type].slots_per_block; ++slot) {
			if (block->slot_info[slot] == SLOT_UNMAPPED) {
				handle = metadata_to_handle(block, block_type, slot);
				ret = pool->ops->evict(pool, handle);
				if (ret)
					break;

				++reclaimed;
				spin_lock(&block->lock);
				block->slot_info[slot] = SLOT_FREE;
				spin_unlock(&block->lock);
				block->free_slots++;
			}
		}
		spin_lock(&tree->lock);
		/* some occupied slots remained - modify coeff and leave the block */
		if (block->free_slots != tree_desc[block_type].slots_per_block) {
			block->under_reclaim = false;
			block->coeff = block->free_slots *
				(tree_desc[block_type].slots_per_block - block->free_slots);
			spin_unlock(&tree->lock);
		} else {
		/* all slots are free - delete this block */
			rb_erase(&block->block_node, &tree->root);
			tree->block_count--;
			spin_unlock(&tree->lock);
			free_pages((unsigned long)block, tree_desc[block_type].order);
		}
		if (reclaimed != 0)
			return reclaimed;
		return -EAGAIN;
	}
	return -EINVAL;
}


/**
 * ztree_map() - maps the allocation associated with the given handle
 * @pool:	pool in which the allocation resides
 * @handle:	handle associated with the allocation to be mapped
 *
 *
 * Returns: a pointer to the mapped allocation
 */
static void *ztree_map(struct ztree_pool *pool, unsigned long handle)
{
	unsigned int block_type, slot;
	struct ztree_block *block;

	block = handle_to_metadata(handle, &block_type, &slot);
	spin_lock(&block->lock);
	block->slot_info[slot] = SLOT_MAPPED;
	spin_unlock(&block->lock);
	return (void *)(block + 1) + slot * tree_desc[block_type].slot_size;
}

/**
 * ztree_unmap() - unmaps the allocation associated with the given handle
 * @pool:	pool in which the allocation resides
 * @handle:	handle associated with the allocation to be unmapped
 */
static void ztree_unmap(struct ztree_pool *pool, unsigned long handle)
{
	unsigned int block_type, slot;
	struct ztree_block *block;

	block = handle_to_metadata(handle, &block_type, &slot);
	spin_lock(&block->lock);
	block->slot_info[slot] = SLOT_UNMAPPED;
	spin_unlock(&block->lock);
}

/**
 * ztree_get_pool_size() - gets the ztree pool size in bytes
 * @pool:	pool whose size is being queried
 *
 * Returns: size in bytes of the given pool.
 */
static u64 ztree_get_pool_size(struct ztree_pool *pool)
{
	u64 total_size;
	int i;

	total_size = 0;
	for (i = 0; i < ARRAY_SIZE(tree_desc); i++) {
		total_size += (pool->block_trees)[i].block_count
				* (PAGE_SIZE << tree_desc[i].order);
	}
	return total_size;
}

/*****************
 * zpool
 ****************/

static int ztree_zpool_evict(struct ztree_pool *pool, unsigned long handle)
{
	if (pool->zpool && pool->zpool_ops && pool->zpool_ops->evict)
		return pool->zpool_ops->evict(pool->zpool, handle);
	else
		return -ENOENT;
}

static const struct ztree_ops ztree_zpool_ops = {
	.evict =	ztree_zpool_evict
};

static void *ztree_zpool_create(const char *name, gfp_t gfp,
				   const struct zpool_ops *zpool_ops,
				   struct zpool *zpool)
{
	struct ztree_pool *pool;

	pool = ztree_create_pool(gfp, &ztree_zpool_ops);
	if (pool) {
		pool->zpool = zpool;
		pool->zpool_ops = zpool_ops;
	}
	return pool;
}

static void ztree_zpool_destroy(void *pool)
{
	ztree_destroy_pool(pool);
}

static int ztree_zpool_malloc(void *pool, size_t size, gfp_t gfp,
			unsigned long *handle)
{
	return ztree_alloc(pool, size, gfp, handle);
}

static void ztree_zpool_free(void *pool, unsigned long handle)
{
	ztree_free(pool, handle);
}

static int ztree_zpool_shrink(void *pool, unsigned int pages,
			unsigned int *reclaimed)
{
	unsigned int total = 0;
	int ret = -EINVAL;

	while (total < pages) {
		ret = ztree_reclaim_block(pool);
		if (ret < 0)
			break;
		total += ret;
	}
	if (reclaimed)
		*reclaimed = total;

	return ret;
}

static void *ztree_zpool_map(void *pool, unsigned long handle,
			enum zpool_mapmode mm)
{
	return ztree_map(pool, handle);
}

static void ztree_zpool_unmap(void *pool, unsigned long handle)
{
	ztree_unmap(pool, handle);
}

static u64 ztree_zpool_total_size(void *pool)
{
	return ztree_get_pool_size(pool);
}

static struct zpool_driver ztree_zpool_driver = {
	.type =		"ztree",
	.owner =	THIS_MODULE,
	.create =	ztree_zpool_create,
	.destroy =	ztree_zpool_destroy,
	.malloc =	ztree_zpool_malloc,
	.free =		ztree_zpool_free,
	.shrink =	ztree_zpool_shrink,
	.map =		ztree_zpool_map,
	.unmap =	ztree_zpool_unmap,
	.total_size =	ztree_zpool_total_size,
};

MODULE_ALIAS("zpool-ztree");

static int __init init_ztree(void)
{
	pr_info("loaded\n");
	zpool_register_driver(&ztree_zpool_driver);
	return 0;
}

static void __exit exit_ztree(void)
{
	zpool_unregister_driver(&ztree_zpool_driver);
	pr_info("unloaded\n");
}

module_init(init_ztree);
module_exit(exit_ztree);

MODULE_LICENSE("GPL");
MODULE_AUTHOR("Ananda Badmaeb <a.badmaev@clicknet.pro>");
MODULE_DESCRIPTION("Block tree allocator for compressed pages");
