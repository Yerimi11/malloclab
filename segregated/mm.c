/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 * 
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.  A block is pure payload. There are no headers or
 * footers.  Blocks are never coalesced or reused. Realloc is
 * implemented directly using mm_malloc and mm_free.
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "week06-05",
    /* First member's full name */
    "Yerim",
    /* First member's email address */
    "sontt4266@naver.com",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};

/***** Segregated *****/
/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)
#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

// Basic constants and macros
#define WSIZE 4
#define DSIZE 8
#define CHUNKSIZE (1<<12)
#define INITCHUNKSIZE (1<<6) // explicit 초기 힙 크기가 6워드짜리 메모리 였으므로.

#define LISTLIMIT 20

// calculate max value
#define MAX(x,y) ((x)>(y) ? (x) : (y))

//size와 할당 여부를 하나로 합친다
#define PACK(size,alloc) ((size)|(alloc))

//포인터 p가 가르키는 주소의 값을 가져온다.
#define GET(p)      (*(unsigned int *)(p))

//포인터 p가 가르키는 곳에 val을 역참조로 갱신
#define PUT(p,val)  (*(unsigned int *)(p)=(val))

//포인터 p가 가르키는 곳의 값에서 하위 3비트를 제거하여 블럭 사이즈를 반환(헤더+푸터+페이로드+패딩)
#define GET_SIZE(p)     (GET(p) & ~0X7)
//포인터 p가 가르키는 곳의 값에서 맨 아래 비트를 반환하여 할당상태 판별
#define GET_ALLOC(p)    (GET(p) & 0X1)

//블럭포인터를 통해 헤더 포인터,푸터 포인터 계산
#define HDRP(bp) ((char*)(bp) - WSIZE)
#define FTRP(bp) ((char*)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

//블럭포인터 -> 블럭포인터 - WSIZE : 헤더위치 -> GET_SIZE으로 현재 블럭사이즈계산 -> 다음 블럭포인터 반환
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
//블럭포인터 -> 블럭포인터 - DSIZE : 이전 블럭 푸터 -> GET_SIZE으로 이전 블럭사이즈계산 -> 이전 블럭포인터 반환
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

//포인터 p가 가르키는 메모리에 포인터 ptr을 입력
#define SET_PTR(p, ptr) (*(unsigned int *)(p) = (unsigned int)(ptr)) // SET_PTR(주소값, value값) p의 주소값을 블럭에 ptr로 담는다

//가용 블럭 리스트에서 next 와 prev의 포인터를 반환
#define NEXT_PTR(ptr) ((char *)(ptr))
#define PREV_PTR(ptr) ((char *)(ptr) + WSIZE)

//segregated list 내에서 next 와 prev의 포인터를 반환
#define PRED(ptr) (*(char **)(ptr))
#define SUCC(ptr) (*(char **)(PREV_PTR(ptr)))

//전역변수 
char *heap_listp = 0;
void *segregated_free_lists[LISTLIMIT]; // 크기별로. 20까지 하는 이유? 코드 짠 사람이 임의로 설정한 값. 아마 최적화이지 않을까.

//함수 목록
static void *coalesce(void *bp);
static void *extend_heap(size_t words);
static void *find_fit(size_t asize);
static void *place(void *bp, size_t asize);
static void insert_node(void *ptr, size_t size);
static void delete_node(void *ptr);

/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    int list;
    
    for (list = 0; list < LISTLIMIT; list++) { // 첫번째만 모은 리스트 20요소의 값은 전부 NULL로 채운다
        segregated_free_lists[list] = NULL; // 초기화해줌
    }
    
    /* Create the initial empty heap */
    if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1)
        return -1;
    PUT(heap_listp, 0);                          /* Alignment padding */
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1)); /* Prologue header */
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1)); /* Prologue footer */
    PUT(heap_listp + (3*WSIZE), PACK(0, 1));     /* Epilogue header */
    heap_listp = heap_listp + (2*WSIZE); // 다른사람들은 이 줄을 없앴네

    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    if (extend_heap(INITCHUNKSIZE) == NULL) // 90점
    // if (extend_heap(CHUNKSIZE/WSIZE) == NULL) : 88점
        return -1;  
    return 0;
}

static void *extend_heap(size_t words){
    char *bp;
    size_t size;

    size = (words % 2) ? (words +1) * WSIZE : words * WSIZE;
    if((bp = mem_sbrk(size)) == (void *)-1)
        return NULL;

    PUT(HDRP(bp),PACK(size,0));
    PUT(FTRP(bp),PACK(size,0));
    PUT(HDRP(NEXT_BLKP(bp)),PACK(0,1)); /* New Epilogue Block */
    insert_node(bp,size);

    return coalesce(bp);
}

static void insert_node(void *ptr, size_t size) {
    int list = 0;
    void *search_ptr = ptr; // 이진탐색트리의 parent 역할, search_ptr부터 크기가 맞는 리스트의 영역으로 들어감
    void *insert_ptr = NULL; //실제 노드가 삽입되는 위치, 이진탐색트리의 child 역할
    
    // Select segregated list 
    while ((list < LISTLIMIT - 1) && (size > 1)) { // 이진수의 3자리 비트 연산, 반복문 한바퀴 돌 때마다 자릿수 하나씩 쉬프트. 
    // 반복문을 모두 빠져나오면, 모두 리스트의 같은 인덱스에 들어가게 됨. 
        size >>= 1; // 쉬프트 : 100 -> 10 -> 1
        list++; // 한 번 돌면서 리스트는 한 번씩 증가.
    }
    
    // Keep size ascending order and search
    search_ptr = segregated_free_lists[list]; // 우리가 넣을 사이즈의 seg의 인덱스를 찾음
    while ((search_ptr != NULL) && (size > GET_SIZE(HDRP(search_ptr)))) {
        insert_ptr = search_ptr;
        search_ptr = PRED(search_ptr);
    }
    
    // Set NEXT and PREV 
    if (search_ptr != NULL) {
        if (insert_ptr != NULL) {
            SET_PTR(NEXT_PTR(ptr), search_ptr); // NEXT_PTR의 ptr을 search_ptr로
            SET_PTR(PREV_PTR(search_ptr), ptr); // PREV_PTR의 search_ptr를 ptr로
            SET_PTR(PREV_PTR(ptr), insert_ptr);
            SET_PTR(NEXT_PTR(insert_ptr), ptr);
        } else {
            SET_PTR(NEXT_PTR(ptr), search_ptr);
            SET_PTR(PREV_PTR(search_ptr), ptr);
            SET_PTR(PREV_PTR(ptr), NULL);
            segregated_free_lists[list] = ptr; // LIFO라 앞에 새로 넣어야해서
        }
    } else {
        if (insert_ptr != NULL) { // 1일 때 NULL로 초기화 되어 있음
            SET_PTR(NEXT_PTR(ptr), NULL);
            SET_PTR(PREV_PTR(ptr), insert_ptr);
            SET_PTR(NEXT_PTR(insert_ptr), ptr);
        } else {
            SET_PTR(NEXT_PTR(ptr), NULL);
            SET_PTR(PREV_PTR(ptr), NULL);
            segregated_free_lists[list] = ptr;
        }
    }
    
    return;
}

static void delete_node(void *ptr) { // ptr가 가리키는 블럭을 삭제 
    int list = 0;
    size_t size = GET_SIZE(HDRP(ptr));
    
    // Select segregated list 
    while ((list < LISTLIMIT - 1) && (size > 1)) {
        size >>= 1;
        list++;
    }
    
    if (PRED(ptr) != NULL) {
        if (SUCC(ptr) != NULL) {
            SET_PTR(PREV_PTR(PRED(ptr)), SUCC(ptr));
            SET_PTR(NEXT_PTR(SUCC(ptr)), PRED(ptr));
        } else {
            SET_PTR(PREV_PTR(PRED(ptr)), NULL);
            segregated_free_lists[list] = PRED(ptr);
        }
    } else {
        if (SUCC(ptr) != NULL) {
            SET_PTR(NEXT_PTR(SUCC(ptr)), NULL);
        } else {
            segregated_free_lists[list] = NULL;
        }
    }
    
    return;
}


/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    size_t asize;
    size_t extendsize; //들어갈 자리가 없을때 늘려야 하는 힙의 용량
    char *bp;

    /* Ignore spurious*/
    if (size == 0)
        return NULL;

    /* Adjust block size to include overhead and alignment reqs. */
    /* 최소 16바이트 크기의 블록 구성. 8바이트 for 정렬 조건 만족 위해, 추가 8바이트 for 헤더, 풋터 오버헤드를 위해 */
    if (size <= DSIZE) {
        asize = 2*DSIZE; // adjust size : 조정된 사이즈. 2*8 = 16 , 8보다 작은 요청값은 다 16으로 만든다
    }
    else { // 8바이트 넘는 요청 : 오버헤드 바이트 내에 더해주고, 인접 8의 배수로 반올림
        asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE); 
    }
    
    /* Search the free lish for a fit */ // find_fit으로 적절한 가용블록을 가용리스트에서 검색
    if ((bp = find_fit(asize)) != NULL) { 
        // 맞는 블록 찾으면 - 할당기 : place로 요청 블록 배치, 옵션으로 초과부분 분할, 새 할당 블록 리턴(반환)
        bp = place(bp, asize); // put해서 bp를 헤더에 asize만큼 넣어준다(할당해준다) 
        return bp;
    }
    /* No fit found. Get more memory and place the block */
    // 못찾으면 : extend_heap으로 힙을 새 가용 블록으로 확장(메모리 공간 더 할당), 요청 블록을 이 새 가용 블록에 배치
    extendsize = MAX(asize,CHUNKSIZE);
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL)
        return NULL;
    
    bp = place(bp, asize); // 필요하면 블럭 분할
    return bp;
}

// 전,후에 free block이 있을시 합쳐줌 + 합쳐지는 경우 segregation_lists에서 기존 free block 노드 삭제해줌
static void *coalesce(void *bp){
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp))); // 이전 블럭 free인지 check
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp))); // 다음 ~
    size_t size = GET_SIZE(HDRP(bp)); // 현재 블럭의 size

    /* case 1 */ // 이전 블럭, 다음 블럭 최하위 bit 둘 다 1 할당이면, 블럭 병합 없이 bp return
    if(prev_alloc && next_alloc){
        return bp;
    }

    /* case 2 */ // 이전 블럭 최하위 bit 1(할당)이고, 다음 블럭 최하위 bit 0(비할당)이면
    else if (prev_alloc && !next_alloc){
        delete_node(bp);
        delete_node(NEXT_BLKP(bp));
        
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp),PACK(size,0));
        PUT(FTRP(bp),PACK(size,0));
    }

    /* case 3 */ // 이전 블럭 최하위 bit 0(비할당), 다음 블럭 최하위 bit 1(할당)이면
    else if (!prev_alloc && next_alloc){
        delete_node(bp);
        delete_node(PREV_BLKP(bp));
        
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp),PACK(size,0));
        PUT(HDRP(PREV_BLKP(bp)),PACK(size,0));
        bp = PREV_BLKP(bp);
    }
    
    /* case 4 */ // 이전 블럭 최하위 bit 0(비할당), 다음 블럭 최하위 bit 0(비할당)이면
    else{
        delete_node(bp);
        delete_node(PREV_BLKP(bp));
        delete_node(NEXT_BLKP(bp));
        
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)),PACK(size,0));
        PUT(FTRP(NEXT_BLKP(bp)),PACK(size,0));
        bp = PREV_BLKP(bp);
    }
    
    insert_node(bp,size);
    return bp;
}

static void *find_fit(size_t asize){

    /* First fit Search */
    char *bp; 
    int list = 0; 
    size_t searchsize = asize;

    // Search for free block in segregated list
    while (list < LISTLIMIT) { // searchsize를 seg_list의 몇번째에 넣을지 찾음
        if ((list == LISTLIMIT - 1) || ((searchsize <= 1) && (segregated_free_lists[list] != NULL))) {
            bp = segregated_free_lists[list];
            // Ignore blocks that are too small or marked with the reallocation bit
            while ((bp != NULL) && ((asize > GET_SIZE(HDRP(bp)))))
            {
                bp = PRED(bp);
            }
            if (bp != NULL)
                return bp;
        }
        
        searchsize >>= 1; // 비트연산자
        list++;
        /* 	(=) searchsize = searchsize >> 1
            ex) 3 >> 1 : 3은 11(2). 1칸 밀면 1 됨 (while문 1 하나 남을 때 까지 돈다)
            i = 1이 되고 리스트 변수에 들어가고 seg_list인덱스로 작용하게 됨
            ex) 4 >> 1 : 100 -> 10, 10 -> 1 두번 쉬프트… i = 2 되고 윗줄이랑 똑같이 적용
            +ex) 3 << 1 : 11 => 110 */
    }

    return NULL; /* no fit */
}

static void *place(void *bp, size_t asize){
    size_t csize = GET_SIZE(HDRP(bp));
    size_t remainder = csize - asize; // 남은 사이즈
    delete_node(bp);

    if (remainder <= 2*DSIZE){ // 남은 사이즈가 16보다 작으면 바로 할당으로 넣기
        PUT(HDRP(bp),PACK(csize,1));
        PUT(FTRP(bp),PACK(csize,1));
    }
    else if(asize >= 100){ // test case기준으로 맞춤..ㅎㅎ 100 기준으로 100보다 작거나 큰 사이즈 몰아서 넣고 free 합침(더 효율적)
        // 요청사이즈가 100보다 크면
        PUT(HDRP(bp),PACK(remainder,0)); // 남은 사이즈만큼 free시키고
        PUT(FTRP(bp),PACK(remainder,0));
        PUT(HDRP(NEXT_BLKP(bp)),PACK(asize,1)); // 요청받은 사이즈 만큼 할당
        PUT(FTRP(NEXT_BLKP(bp)),PACK(asize,1));
        insert_node(bp,remainder);
        return NEXT_BLKP(bp);
    }
    else{ // 16 < aszie < 100 이면
        PUT(HDRP(bp),PACK(asize,1)); // 할당
        PUT(FTRP(bp),PACK(asize,1)); 
        PUT(HDRP(NEXT_BLKP(bp)),PACK(remainder,0)); // 남은 사이즈만큼 넥스트가 프리 됨
        PUT(FTRP(NEXT_BLKP(bp)),PACK(remainder,0));
        insert_node(NEXT_BLKP(bp),remainder);
    }
    return bp;
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp));

    PUT(HDRP(bp),PACK(size,0));
    PUT(FTRP(bp),PACK(size,0));
    
    insert_node(bp,size);

    coalesce(bp);
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    void *oldptr = ptr;
    void *newptr;
    size_t copySize;
    
    newptr = mm_malloc(size);
    if (newptr == NULL)
      return NULL;
    // copySize = *(size_t *)((char *)oldptr - SIZE_T_SIZE);
    copySize = GET_SIZE(HDRP(oldptr));
    if (size < copySize)
      copySize = size;
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;
}