/*
 * mm.c - Explicity free list Implementation
 *
 * Timothy Kaboya - tkaboya
 * HLD Description of my solution 
 * 1. Doubly linked Explicit List
 * 2. First Fit 
 *
 *  VIRTUAL MEMORY STRUCTURE 
 *  Free block
 *  [ HEADER | PREV | NEXT |    PAYLOAD    | FOOTER ]
 *  Allocated block
 *  [ HEADER |   PAYLOAD    | FOOTER ]
 *   
 *  Free List Structure
 *  [NULL  <==  Free 1 <==> Free 2 <==> Free3 <==> ... <==> FreeN ==> NULL]
 *
 * MALLOC - Uses First Fit and if block too big, block is split to
 * create new free block. 
 *
 * FREE - Find block and set its alloc bits to 0. Then append newly freed block
 * using the coalesce function that coalesces it w/ free neighbours
 *
 * REALLOC - If new size < old size, truncate new block
 * if remaining block is larger than mini add it to free list 
 * When new size > old size, just copy old size till its end
 *
 * CALLOC - Malloc for given size and then all blocks to zero. 
 *
 */
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "mm.h"
#include "memlib.h"

/* do not change the following! */
#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#define checkheap mm_checkheap
#endif /* def DRIVER */


/* If you want debugging output, use the following macro.  When you hand
 * in, remove the #define DEBUG line. */
/* #define DEBUG  */
#ifdef DEBUG
# define dbg_printf(...) printf(__VA_ARGS__)
#else
# define dbg_printf(...)
#endif


/* Basic constants and macros */
#define WSIZE       4       /* Word and header/footer size (bytes) */ 
#define DSIZE       8       /* Double word size (bytes) */
#define CHUNKSIZE  (1<<8)  /* Extend heap by this amount (bytes) */  
#define ALIGNMENT 8         /* single word (4) or double word (8) alignment */
#define MINIMUM   24

#define MAX(x, y) ((x) > (y)? (x) : (y))
/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(p) (((size_t)(p) + (ALIGNMENT-1)) & ~0x7)

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc)  ((size) | (alloc))

/* Read and write a word at address p */
#define GET(p)       (*(unsigned int *)(p))
#define PUT(p, val)  (*(unsigned int *)(p) = (val))

/* Read the size and allocated fields from address p */
#define GET_SIZE(p)  (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

/* Given block ptr ptr, compute address of its header and footer */
#define HDRP(ptr)       ((char *)(ptr) - WSIZE)
#define FTRP(ptr)       ((char *)(ptr) + GET_SIZE(HDRP(ptr)) - DSIZE)

/* Given block ptr ptr, compute address of next and previous blocks */
#define NEXT_BLKP(ptr)  ((char *)(ptr) + GET_SIZE(HDRP(ptr)))
#define PREV_BLKP(ptr)  ((char *)(ptr) - GET_SIZE(HDRP(ptr) - WSIZE))

/* Given free list ptr, compute address of next and previous free list ptrs */
#define NEXT_FREEP(ptr)  (*(char **)((char *)(ptr) + DSIZE))
#define PREV_FREEP(ptr)  (*(char **)((char * )(ptr)))

/* Global variables */
static char *heap_listp = 0;  /* Pointer to first block */
static char *free_listp = 0;   /* Pointer to list to list of free blocks */ 

/* Function prototypes for internal helper routines */
static void *extend_heap(size_t words);
static void place(void *ptr, size_t asize);
static void *find_fit(size_t asize);
static void *coalesce(void *ptr);
/* My own helpers: :) */
static void printblock(void *ptr);
static void checkblock(void *ptr);
static void insertfreeblock(void *ptr);
static void removefreeblock(void *ptr);
static int freelistedge(void *ptr);
/*
 * Initialize memory manager: return -1 on error, 0 on success.
 * Memory is essentially one huge block that is in free list. 
 */
int mm_init(void) {

    /* Create the initial empty heap(free list) */
    if ((heap_listp = mem_sbrk(2*MINIMUM)) == (void *)-1) 
        return -1;
    PUT(heap_listp, 0);                          /* Alignment padding */
    PUT(heap_listp + (1*WSIZE), PACK(MINIMUM, 1)); /* Prologue header */ 
    PUT(heap_listp + (2*WSIZE), 0); /* Previous pointer */
    PUT(heap_listp + (3*WSIZE), 0);    /* Next Pointer */

    PUT(heap_listp + MINIMUM, PACK(MINIMUM, 1));      /* Prologue footer */
    PUT(heap_listp + MINIMUM + WSIZE, PACK(0, 1));    /* Epilogue Header */

    free_listp = heap_listp + DSIZE;

    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL) 
        return -1;

    return 0;
}

/*
 * malloc - Allocate a block with at least size bytes of payload
 */
void *malloc (size_t size) {
    size_t asize;      /* Adjusted block size */
    size_t extendsize; /* Amount to extend heap if no fit */
    char *ptr;  


    if (heap_listp == 0){
        mm_init();
    }


    /* Ignore spurious requests */
    if (size == 0)
        return NULL;


    /* Adjust block size to include overhead and alignment reqs. */
    asize = MAX(ALIGN(size) + DSIZE, MINIMUM);

    /* Search the free list for a fit */
    if ((ptr = find_fit(asize)) != NULL) {  
        place(ptr, asize);       
        return ptr;
    }

    /* No fit found. Get more memory and place the block */
    extendsize = MAX(asize,CHUNKSIZE);                 
    if ((ptr = extend_heap(extendsize/WSIZE)) == NULL)  
        return NULL;                                  
    place(ptr, asize);                                 


    return ptr;
}

/*
 * free - Free a block
 */
void free (void *ptr) {


    if (ptr == 0) 
        return;

    size_t size = GET_SIZE(HDRP(ptr));
    if (heap_listp == 0){
        mm_init();
    }

    /* Set header, footer alloc bits to zero */
    PUT(HDRP(ptr), PACK(size, 0));
    PUT(FTRP(ptr), PACK(size, 0));

    coalesce(ptr);

}

/*
 * realloc - Naive implementation of realloc
 */
void *realloc(void *ptr, size_t size) {
    size_t oldsize, asize;
    void *newptr;

    asize = MAX(ALIGN(size) + DSIZE, MINIMUM);
    /* If size == 0 then this is just free, and we return NULL. */
    if(size == 0) {
        free(ptr);
        return 0;
    }

    /* If oldptr is NULL, then this is just malloc. */
    if(ptr == NULL) {
        return malloc(size);
    }


    /* Original block size */
    oldsize = GET_SIZE(HDRP(ptr));

    /* If new size is same as old, just return */
    if (asize == oldsize)  return ptr;


    newptr = mm_malloc(size);

    /* If realloc() fails the original block is left untouched  */
    if(!newptr) {
        return 0;
    }

    /* Copy the old data. */
    if(size < oldsize) oldsize = size;
    memcpy(newptr, ptr, oldsize);

    /* Free the old block. */
    free(ptr);

    return newptr;
}

/*
 * calloc - Allocate the block and set it to zero
 *
 */
void *calloc (size_t nmemb, size_t size) {
    size_t bytes = nmemb * size;
    void *newptr;

    newptr = malloc(bytes);
    memset(newptr, 0, bytes);

    return newptr;
}


/*
 * Return whether the pointer is in the heap.
 * May be useful for debugging.
 */
static int in_heap(const void *p) {
    return p <= mem_heap_hi() && p >= mem_heap_lo();
}

/*
 * Return whether the pointer is aligned.
 * May be useful for debugging.
 */
static int aligned(const void *p) {
    return (size_t)ALIGN(p) == (size_t)p;
}

/* 
 * mm_checkheap - 
 * Heap Checker first checks on a block by block basis for inconsistency
 * In this order
 * - Prologue block. 
 * - Iterate through list till epilogue block
 *   On each block, call the checkblock function to check block.
 *   Count number of free blocks
 * 
 * Check ending epilogue block
 *
 * Then we check free list. 
 * - Iterate over entire free list
 *    Check for Prev/Next Allocate consistency
 *    All pointers are between heap
 *
 * Compare Block free list count to actual free list count
 *
 */
void mm_checkheap(int lineno) {
    void *ptr;
    int numfree1 = 0, numfree2 = 0;     /* Count free blocks */
    ptr = heap_listp;                   /* Start from the first block address */

    /* Check prologue */ 
    if ((GET_SIZE(HDRP(ptr)) != MINIMUM) || (GET_ALLOC(HDRP(ptr)) != 1)) {
        printf("Addr: %p - ** Prologue Error** \n", ptr);
        assert(0);
    }
    ptr = NEXT_BLKP(ptr);

    /* Iterating through entire heap. Convoluted code checks that
     * we are not at the epilogue. Loops thr and checks epilogue block! */
    while (!((GET_SIZE(HDRP(ptr)) == 0) && (GET_ALLOC(HDRP(ptr)) == 1))) {

        /* Perform all checks done on block */
        checkblock(ptr);
        /* Check coalescing: If alloc bit of current and next block is 0 */
        if (!(GET_ALLOC(HDRP(ptr)) || GET_ALLOC(HDRP(NEXT_BLKP(ptr))))) {
            printf("Addr: %p - ** Coalescing Error** \n", ptr);
            assert(0);
        }

        /* Count number of free blocks */
        if(!(GET_ALLOC(HDRP(ptr))))
            numfree1++;

        ptr = NEXT_BLKP(ptr);
    }


    /* Heap Check for explicit list */ 
    ptr = free_listp;     

    /* If our free list is empty, nothing to check */
    if (ptr == 0) {
        return;
    }


    /* Iterating through free list */ 
    while (ptr != NULL) {
        if (!freelistedge(ptr)) {
            /* All next/prev pointers are consistent */
            if (PREV_FREEP(NEXT_FREEP(ptr)) != NEXT_FREEP(PREV_FREEP(ptr))) {
                printf("Addr: %p - ** Next/Prev Consistency Error ** \n", ptr);
                assert(0);
            }
        }
        /* Free List bounds check */ 
        if (!in_heap(ptr)) {
            printf("Addr: %p - ** Free List Out of bounds** \n", ptr);
            assert(0);
        }
        numfree2++; 

        ptr = NEXT_FREEP(ptr);
    }

    if (numfree1 != numfree2) {
        printf(" Error: - ** %d Free List Count %d ** \n", numfree1, numfree2);
        assert(0);
    }

}


/********  The remaining routines are internal helper routines  **************/

/* 
 * extend_heap - Extend heap with free block and return its block pointer
 */
static void *extend_heap(size_t words) 
{
    char *ptr;
    size_t size;

    /* Allocate an even number of words to maintain alignment */
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE; 
    if (size < MINIMUM)
        size = MINIMUM;
    if ((long)(ptr = mem_sbrk(size)) == -1)  
        return NULL;                                        

    /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(ptr), PACK(size, 0));         /* Free block header */   
    PUT(FTRP(ptr), PACK(size, 0));         /* Free block footer */   
    PUT(HDRP(NEXT_BLKP(ptr)), PACK(0, 1)); /* New epilogue header */ 

    /* Coalesce if the previous block was free */
    return coalesce(ptr);                                          
}

/*
 * coalesce - Boundary tag coalescing. Returns ptr to coalesced block
 * Function: Coalesce newly freed block with neighbours, if no neighbour
 * is free, just append new free block to list. 
 *
 * To coalesce newly freed block with neighbours, these are the possibilities
 *    [PREV -  CURR - NEXT ]
 *      ||      ||     ||
 *      ||      ||     ||
 * 1: [ALLOC - FREE - ALLOC  ] Result: Just append new block to list
 * 2: [FREE  - FREE - ALLOC  ] Result: Append new block (PREV + CURR)
 * 3: [ALLOC - FREE - FREE   ] Result: Append new block (CURR + NEXT)
 * 4: [FREE  - FREE - FREE   ] Result: Apppend new block (PREV  + CURR + NEXT)
 */
static void *coalesce (void *ptr) 
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(ptr)));
    /* When at front, prev block is same as curr block :( Nasty bug it was */
    if (PREV_BLKP(ptr) == ptr )
        prev_alloc = 1;

    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(ptr)));
    size_t size = GET_SIZE(HDRP(ptr));

    /* Case  1 constructed as fall through scenario */ 

    if (prev_alloc && !next_alloc) {      /* Case 2 */
        size += GET_SIZE(HDRP(NEXT_BLKP(ptr)));
        removefreeblock(NEXT_BLKP(ptr));           /* remove next block */        
        PUT(HDRP(ptr), PACK(size, 0));
        PUT(FTRP(ptr), PACK(size,0));
    }

    else if (!prev_alloc && next_alloc) {      /* Case 3 */
        size += GET_SIZE(HDRP(PREV_BLKP(ptr)));
        removefreeblock(PREV_BLKP(ptr));          /* remove previous block */
        PUT(FTRP(ptr), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(ptr)), PACK(size, 0));
        ptr = PREV_BLKP(ptr);
    }

    else if (!prev_alloc && !next_alloc){      /* Case 4 */
        size += GET_SIZE(HDRP(PREV_BLKP(ptr))) + 
            GET_SIZE(FTRP(NEXT_BLKP(ptr)));
        removefreeblock(NEXT_BLKP(ptr));           /* remove next block */        
        removefreeblock(PREV_BLKP(ptr));         /* remove previous block */
        PUT(HDRP(PREV_BLKP(ptr)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(ptr)), PACK(size, 0));
        ptr = PREV_BLKP(ptr);
    }


    /* Insert Coalesced block in free list */
    insertfreeblock(ptr);       

    return ptr;
}

/* 
 * place - Place block of asize bytes at start of free block ptr 
 *         Remove free block. 
 *         if remainder < minimum block size, split it up and append it as a 
 *         free block by calling coalesce function. 
 *
 */
static void place(void *ptr, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(ptr));   


    if ((csize - asize) >= (MINIMUM)) { 
        PUT(HDRP(ptr), PACK(asize, 1));
        PUT(FTRP(ptr), PACK(asize, 1));
        removefreeblock(ptr);
        ptr = NEXT_BLKP(ptr);
        PUT(HDRP(ptr), PACK(csize-asize, 0));
        PUT(FTRP(ptr), PACK(csize-asize, 0));
        coalesce(ptr);
    }
    else { 
        PUT(HDRP(ptr), PACK(csize, 1));
        PUT(FTRP(ptr), PACK(csize, 1));
        removefreeblock(ptr);
    }

}

/* 
 * find_fit - Find a fit for a block with asize bytes
 *            Iterate over free list until we get 
 *            free block >= requested asize
 */
static void *find_fit (size_t asize)
{
    /* First-fit search */
    void *ptr;

    /* Iterate over free list till we find the first block that fits */
    for (ptr = free_listp; ptr != NULL; ptr = NEXT_FREEP(ptr)) {
        if (!GET_ALLOC(HDRP(ptr)) && (asize <= GET_SIZE(HDRP(ptr)))) {
            return ptr;
        }
    }
    return NULL; /* No fit */
}


/* 
 * Print block - print block header and footer. 
 * For debugging purposes
 */
static void printblock(void *ptr)  {
    size_t hsize, fsize;
    size_t halloc, falloc;
    hsize = GET_SIZE(HDRP(ptr));
    fsize = GET_SIZE(FTRP(ptr));
    halloc = GET_ALLOC(HDRP(ptr));
    falloc = GET_ALLOC(FTRP(ptr));

    if (ptr == NULL ) {
        printf("Error: Null Pointer Address!! \n");
        return;
    }
    printf("Addr: %p, Hdr: [%zu:%c], Ftr: [%zu:%c] \n",
            ptr, hsize, (halloc ? 'a':'f'), fsize, (falloc ? 'a':'f'));
    if (hsize == 0 && halloc == 1)
        printf("Addr: %p - EOF Block \n", ptr); 
}


/* 
 * checkblock - check block header and footer. 
 *
 * It is called by the Check Heap Function. 
 * Performs all checks done on each block. 
 *
 * These are 
 * - Minimum size
 * - Bounds checking
 * - Address alignment
 * Header and footer match
 */
static void checkblock(void *ptr)  {
    /* Check each block's address alignment */
    if (!aligned(ptr)) {
        printf("Addr: %p - ** Block Alignment Error** \n", ptr);
        assert(0);
    }
    /* Each block's bounds check */ 
    if (!in_heap(ptr)) {
        printf("Addr: %p - ** Out of Heap Bounds Error** \n", ptr);
        assert(0);
    }
    /* Check Minimum size */
    if (GET_ALLOC(HDRP(ptr))) {
        if (GET_SIZE(HDRP(ptr)) < (2*DSIZE)) {
            printf("Addr: %p - ** Min Size Error ** \n", ptr);
            assert(0);
        }
    }
    /* Header/Footer Alignmment */
    if (GET_SIZE(HDRP(ptr)) % ALIGNMENT)  {
        printf("Addr: %p - ** Header Not double word aligned** \n", ptr);
        assert(0);
    }

    /* Check header: footer match */
    if ((GET_SIZE(HDRP(ptr)) != GET_SIZE(FTRP(ptr))) ||
            (GET_ALLOC(HDRP(ptr)) != GET_ALLOC(FTRP(ptr)))) {
        printf("Addr: %p - ** Header Footer mismatch** \n", ptr);
        printblock(ptr);
        assert(0);
    }

}


/* 
 * insertfreeblock - Append free block to the front of list
 *                   Link new block to current free list and
 *                   set new block as top of current list. 
 */
static void insertfreeblock(void *ptr) {
    /* If our free list has nothing, set it.  */ 
    if (free_listp == NULL) {
        NEXT_FREEP(ptr) = NULL;
        PREV_FREEP(ptr) = NULL;
        free_listp = ptr;
        return;
    }

    PREV_FREEP(ptr) = NULL;
    NEXT_FREEP(ptr) = free_listp;       /* Set curr next to head of list */
    PREV_FREEP(free_listp) = ptr;                

    free_listp = ptr;                   /* curr ptr is now head of list */
}


/* 
 * removefreeblock - Remove freed block from the list. 
 *      Coded to reflect all possible cases to avoid ambiguity
 *      CASE 1: Remove block with only one block in the list
 *      CASE 2: Block is top of list: Set next block as new top. 
 *      CASE 3: Block is end of free list: Set prev block as new end
 *      CASE 4: Freed block is a middle one: Link Prev block to next block
 *
 */
static void removefreeblock(void *ptr) {
    /* Case when we have nothing in list */
    if (free_listp == 0)
        return;


    /* Case 1 */
    if ((PREV_FREEP(ptr) == NULL) && (NEXT_FREEP(ptr) == NULL)) {
        free_listp = 0;
    }

    /* Case 2 */
    else if ((PREV_FREEP(ptr) == NULL) && (NEXT_FREEP(ptr) != NULL)) {
        free_listp = NEXT_FREEP(ptr);
        PREV_FREEP(free_listp) = NULL;  
    }

    /* Case 3 */
    else if ((PREV_FREEP(ptr) != NULL) && (NEXT_FREEP(ptr) == NULL)) {
        /* Last one now points to NULL */
        NEXT_FREEP(PREV_FREEP(ptr)) = NULL; 
    }

    /* Case 4 */
    else if ((PREV_FREEP(ptr) != NULL) && (NEXT_FREEP(ptr) != NULL)) {
        PREV_FREEP(NEXT_FREEP(ptr)) = PREV_FREEP(ptr);  
        NEXT_FREEP(PREV_FREEP(ptr)) = NEXT_FREEP(ptr); 
    }

}


/* 
 * freelistedge - Returns 1 is free list ptr is at edge of list. 
 *                This check is used to handle edge conditions in checkblock. 
 */
static int freelistedge(void *ptr) {
    return ((NEXT_FREEP(ptr) == NULL) || (PREV_FREEP(ptr) == NULL));
}
