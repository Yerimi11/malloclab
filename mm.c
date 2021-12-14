/*
 * malloclab - Implemented with an explicit free list allocator to manage allocation of and
 * freeing of memory.  
 *
 * Block structures:
 * An explicit list uses the payload to embed pointers to the previous and next free blocks
 * within a free block. The free and allocated block organizations are shown below:
 *
 * Allocated Block          Free Block
 *  ---------               ---------
 * | HEADER  |             | HEADER  |
 *  ---------               ---------
 * |         |             |  NEXT   |
 * |         |              ---------
 * | PAYLOAD |             |  PREV   |
 * |         |              ---------
 * |         |             |         |
 *  ---------              |         |
 * | FOOTER  |              ---------
 *  ---------              | FOOTER  |
 *                          ---------
 * /
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

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7) // ptr에 7byte를 더한 위치에서 allocate bit를 제거
                    // align으로 크기 맞춰줌 (1칸 뺌) & 비트마스크
                    // 0x7(주소) = 7 = 111(2) // ~은 not. 전부 뒤집어져서 111 -> 000
                    // 아무 숫자 15321341 111 & 000 -> 은 000이 되니까 값을 지워줄 수 있게 됨. 이 이후에 포인터 앞으로 다시 보냄


#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

/* p.825 */
/* Basic constants and macros */
#define WSIZE       4           /* Word and header/footer zise (bytes) */
#define DSIZE       8           /* Double word size (bytes) */
#define CHUNKSIZE   (1<<10)     /* Extend heap by this amount (bytes) */ //초기 힙 사이즈 설정
                // '<<' : 비트쉬프트 : 1을 2진법으로 12칸 보내겠다 - 0이 12개 붙음 -> 1 -> 1000000000000

#define OVERHEAD 8
#define MAX(x, y) ((x) > (y)? (x) : (y))

/* PAck a size and allocated bit into a word */ // 처음에 최하위 3bit를 떼었으니 malloc후 생긴 새로운 값을 묶음
#define PACK(size, alloc)   ((size) | (alloc)) // size와 alloc의 값을 한 word로 묶고, 이를 이용해 h와 f에 쉽게 저장.
                                // '|' : or 연산자
/* Read and write a word at address p */ 
#define GET(p)      (*(unsigned int *)(p)) // 포인터 p가 가리키는 곳의 한 word 값을 읽어온다 
#define PUT(p, val) (*(unsigned int *)(p) = (val)) // 포인터 p가 가리키는 곳의 한 word의 값에 val를 기록 
                    // unsigned int > size_t로 바꾸기
/* Read the size and allocated fields from address p */
#define GET_SIZE(p)     (GET(p) & ~0x7) // 포인터 p가 가리키는 곳에서 한 word를 읽은 다음 하위 3bit를 버린다. 즉, header에서 block size를 읽는다.
#define GET_ALLOC(p)    (GET(p) & 0x1) // 포인터 p가 가리키는 곳에서 한 word를 읽은 다음 최하위 1bit를 읽는다. 1할당, 0노할당

/* Given block ptr bp, compute address of its geader and footer */
#define HDRP(bp)        ((char *)(bp) - WSIZE) // 주어진 포인터 bp의 header(-4)의 주소를 계산 // bp : 페이로드가 시작되는 부분
#define FTRP(bp)        ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE) // 주어진 포인터 bp의 footer 주소 계산
                                    // GET_SIZE(4) - 8 : 헤더값이 포함된 size - 헤더, 풋터값(8)
                    // (char *)(bp) : bp 포인터가 가리키는 블록의 주소를 얻어온다
                    // 헤더에서 3비트빼면 getsize에서 블록 전체의 헤더뺀 사이즈를 얻음
                    // bp : 페이로드의 시작 ptr. = 블록의 시작이 아님
                    // 푸터는 헤더의 카피. 그래서 똑같이 4를 돌아가면 푸터의 시작점을 알 수 있음

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp)   ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE))) // 주어진 포인터 bp를 이용해서 다음 블록 주소 얻어옴
#define PREV_BLKP(bp)   ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE))) // 이전 블록 주소 얻어옴
// 빼주면 윗 블럭의 사이즈를 알 수 있다

static void *heap_listp;
static char *next_ptr;
static void *extend_heap(size_t words);
static void *coalesce(void *ptr);
static void *find_fit(size_t a_size);
static void place(void *bp, size_t a_size);

/* 
 * mm_init - initialize the malloc package.
 *         - Initializes the heap like that shown below.
 *  ____________                                                    _____________
 * |  PROLOGUE  |                8+ bytes or 2 ptrs                |   EPILOGUE  |
 * |------------|------------|-----------|------------|------------|-------------|
 * |   HEADER   |   HEADER   |        PAYLOAD         |   FOOTER   |    HEADER   |
 * |------------|------------|-----------|------------|------------|-------------|
 * ^            ^            ^       
 * heap_listp   free_listp   bp 
 * 
 */
int mm_init(void)
{ // 할당기 : 초기화 완료 후, 어플리케이션으로부터 할당과 반환 요청을 받을 준비를 완료한다. 
    /* Create the initial empty heap */
    if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1) { // sbrk로 4워드(16바이트)할당 : 빈 가용 리스트 만들도록 초기화. 
    // mem_sbrk 함수 돌리면 내가 넣은 인풋값만큼의 영역이 있는지 찾아보고 있으면 그 포인터주소를 heap_listp에 반환하고 아니면 -1 리턴하는 함수. 최소 16바이트인데 16바이트만큼 넣을 공간이 없으면 에러라서 조건문에 들어가서 -1 반환
        return -1; 
    }
    
    PUT(heap_listp, 0);                         /* Alignment padding */ // 첫번째 워드 : 더블워드 경계로 정렬된 미사용 패딩워드
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1)); /* Prologue header */ // 헤더 + 풋터로만 구성된 8바이트 할당 블록, 프롤로그 블록 - 초기화 과정에서 생성, 절대 반환X
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1)); /* Prologue footer */ 
    PUT(heap_listp + (3*WSIZE), PACK(0, 1));     /* Epilogue header */ // 힙 : 에필로그 블록으로 끝남, 헤더로만 구성된 크기가 0 으로 할당된 블록
    heap_listp += (2*WSIZE); // 현재 위치를 나타내는 포인터. 2워드 뒤로 옮긴다


    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL) { // 힙을 CHUCKSIZE바이트로 확장, 초기 가용 블록 생성.
        return -1;                              // Next fit을 이용할 경우, next_ptr를 heap_listp로 초기화한다.
    }
    return 0;
}


static void *extend_heap(size_t words) /* 새 가용 블록으로 힙을 확장하는 함수 */
{
    char *bp;
    size_t size;

    /* Allocate an even number of words to maintain alignment */
    // 요청한 크기를 인접 2워드의 배수로 반올림, 그 후에 sbrk로 메모리시스템으로부터 추가적인 힙 공간 요청
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE; // 나머지가 0 : false, 그 외 : true -> 8의배수로 맞춰짐
    if ((long)(bp = mem_sbrk(size)) == -1) { // long : 정수타입 8바이트 (int 4바이트) // long 빼고 if ((bp = mem_sbrk(size)) == (void *)-1) 으로 써도 됨 // 여기서 mem_sbrk가 size요청받은 만큼 힙을 확장, H, F, P다 생김
        return NULL;
    }

    /* Initialize(초기화) free block header/footer and the epilogue header */
    PUT(HDRP(bp), PACK(size, 0));           /* Free block header */ // 한 칸 뒤로가면서 해당 칸 0(free)시키면서 그 자리를 H로 풋 됨.
    PUT(FTRP(bp), PACK(size, 0));           /* Free block footer */ // 
    // HDRP에 헤더값이 들어있으니 헤더값을 알면 그 블록의 사이즈, 정보를 다 아니까 GET_SIZE로 H, F, P값 다 불러옴 프리 블록의 bp는 힙의 끝에 있음. 거기서 -8한 부분을 푸터로 바꿔준다
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));   /* New epilogue header */

    /* Coalesce if the previous block was free */
    return coalesce(bp);
}


/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size) // malloc : size 바이트의 메모리 블록을 요청
{ // 원래 써있던 코드
    // int newsize = ALIGN(size + SIZE_T_SIZE);
    // void *p = mem_sbrk(newsize);
    // if (p == (void *)-1) {
	// return NULL;
    // }
    // else {
    //     *(size_t *)p = size;
    //     return (void *)((char *)p + SIZE_T_SIZE);
    // }

    // 여기부터 교재 P.828
    size_t asize;       /* Adjusted block size */
    size_t extendsize;  /* Amount to extend heap if no fit */
    char *bp;

    /* Ignore spurious requests */
    if (size == 0) { // 입력받은 사이즈가 0이라면 무시
        return NULL;
    }

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
        place(bp, asize); // put해서 bp를 헤더에 asize만큼 넣어준다(할당해준다) 
        return bp;
    }

    /* No fit found. Get more memory and place the block */ 
    // 못찾으면 : extend_heap으로 힙을 새 가용 블록으로 확장(메모리 공간 더 할당), 요청 블록을 이 새 가용 블록에 배치
    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL) {
        return NULL;
    }
    place(bp, asize); // 필요하면 블록 분할
    return bp;
}

static void *find_fit(size_t a_size) { 
        /* Next fit search */
        char *ptr = next_ptr;
                // ptr위치부터 ; get_size끝까지 ; 다음 블록으로 한 칸씩 이동
        for (ptr = NEXT_BLKP(ptr); GET_SIZE(HDRP(ptr)); ptr = NEXT_BLKP(ptr)) {
            if (!GET_ALLOC(HDRP(ptr)) && GET_SIZE(HDRP(ptr)) >= a_size) { // free이고, 남은 공간 size가 여유가 있으면
                return ptr;
            }
        }
        ptr = heap_listp;
        for (ptr = NEXT_BLKP(ptr); GET_SIZE(HDRP(ptr)); ptr = NEXT_BLKP(ptr)) {
            if (!GET_ALLOC(HDRP(ptr)) && GET_SIZE(HDRP(ptr)) >= a_size) {
                return ptr;
            }
        }
        return NULL;

        // 방법 2)
        // char *bp;
        // // next_ptr에서 리스트의 끝까지 검색
        // for (bp = next_ptr ; GET_SIZE(HDRP(bp)) > 0 ; bp = NEXT_BLKP(bp)) {
        //     if(!GET_ALLOC(HDRP(next_ptr)) && (a_size <= GET_SIZE(HDRP(n\ext_ptr)))) {
        //         return next_ptr;
        //     }
        // }
        // // 리스트의 시작에서 이전의 next_ptr까지 검색
        // for(next_ptr = heap_listp ; next_ptr < bp ; next_ptr = NEXT_BLKP(next_ptr)) {
        //     if(!GET_ALLOC(HDRP(next_ptr)) && (a_size <= GET_SIZE(HDRP(next_ptr)))) {
        //         return next_ptr;

//     /* first fit search */
//     void *bp;
//     // for (bp 여기부터, n>0까지; 다음블록으로 이동) 
                // > 0 까지 찾는 이유 : 끝까지 찾고나면 에필로그블록의 사이즈가 0이니까. 0이 되면 탈출조건이니까 에필로그(0)을 만날 때 루프가 돌아야 해서!.
//     for (bp = (char *)heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
//         if (!GET_ALLOC(HDRP(bp)) && (a_size <= GET_SIZE(HDRP(bp)))) {
//             return bp;
//         }
//     }
//     return NULL; /* No fit */ // 끝가지 돌았는데 없을 때 NULL값 리턴
// }
}

static void place(void *bp, size_t a_size) {
/* 요청 블록을 가용 블록 시작 부분에 배치하여, 나머지 부분 크기가 최소 블록 크기와 같거나 큰 경우에만 분할 */
/* 블록을 배치한 후에 나머지 부분의 크기가 최소 블록 크기와 같거나 크다면, 블록을 분할.
    다음 블록으로 이동하기 전에 새롭게 할당한 블록을 배치해야 한다 */
    size_t c_size = GET_SIZE(HDRP(bp)); // current_size

    // 배치 후에 이 블록의 나머지가 최소 블록의 크기와 같거나 크다면, 블록을 분할해야 한다. (필요한 만큼 할당하고, 남은 공간 0 해주기)
    if ((c_size - a_size) >= (2 * (DSIZE))) { // 최소 16보다 큰 경우에 대해서. c가 현재 블록의 크기, a가 우리가 넣으려는 크기. 둘 빼서 들어갈 수 있는지.
        // 요청 용량 만큼 새롭게 할당한 블록 배치
        PUT(HDRP(bp), PACK(a_size, 1)); // 일단은 요청받은 사이즈만큼 할당을 해준다 : 헤더
        PUT(FTRP(bp), PACK(a_size, 1)); // 푸터
        bp = NEXT_BLKP(bp); // 다음 블록으로 이동
        // 그 다음, 요청받은 사이즈만큼 할당 하고 남은 블럭에 남은 사이즈 만큼의 Free 블록을 만들어준다. 0짜리 header, footer 배치
        PUT(HDRP(bp), PACK(c_size - a_size, 0));
        PUT(FTRP(bp), PACK(c_size - a_size, 0));
    }
    else { // 아니면 현재 사이즈가 남아있는 블록의 크기랑 똑같다면 그냥 그대로 전체 통째로 할당.
        PUT(HDRP(bp), PACK(c_size, 1));
        PUT(FTRP(bp), PACK(c_size, 1));
    }
}

/*
 * mm_free - Freeing a block does nothing.
 */ // 이전에 할당한 블록을 free함수를 호출해서 반환한다 : 요청 블록을 반환하고, 인접 가용 블록들을 coalesce로 통합한다.
void mm_free(void *ptr) 
{
    if(!ptr) return; // 잘못된 free요청일 경우 함수 종료, 이전 프로시져로 return

    size_t size = GET_SIZE(HDRP(ptr)); // ptr의 헤더에서 block size 읽어 옴
    
    // 실제로 데이터를 지우는 게 아니라 header와 footer의 최하위 1비트(할상된 상태)만을 수정
    PUT(HDRP(ptr), PACK(size, 0)); // ptr의 header에 block size와 alloc = 0을 저장
    PUT(FTRP(ptr), PACK(size, 0)); // ptr의 footer에 block size와 alloc = 0을 저장
    coalesce(ptr); // 주위에 빈 블럭이 있을 시 병합
}

static void *coalesce(void *ptr) /* free 시킬 때 (현재 블록을 반환할 때) 사용 */
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(ptr))); // 이전 블럭 할당 여부; no=0, yes=1
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(ptr))); // 다음 ~
    size_t size = GET_SIZE(HDRP(ptr)); // 현재 블럭의 size
    
    /* case 1 */ // 이전 블럭, 다음 블럭 최하위 bit 둘 다 1 할당이면, 블럭 병합 없이 bp return
    if (prev_alloc && next_alloc) {
        next_ptr = ptr; // 이거없으면 next fit 작동 안됨.
        return ptr;
    }

    /* case 2 */ // 이전 블럭 최하위 bit 1(할당)이고, 다음 블럭 최하위 bit 0(비할당)이면, 다음 블럭과 병합한 뒤 bp return
    else if (prev_alloc && !next_alloc) {
        size += GET_SIZE(HDRP(NEXT_BLKP(ptr)));
        PUT(HDRP(ptr), PACK(size, 0)); // alloc을 0으로 -> 프리로 바꿈
        PUT(FTRP(ptr), PACK(size, 0));
    }

    /* case 3 */ // 이전 블럭 최하위 bit 0(비할당), 다음 블럭 최하위 bit 1(할당)이면, 이전 블럭과 병합한 뒤 새로운 bp return
    else if (!prev_alloc && next_alloc) {
        size += GET_SIZE(HDRP(PREV_BLKP(ptr)));
        PUT(HDRP(PREV_BLKP(ptr)), PACK(size, 0));
        PUT(FTRP(ptr), PACK(size, 0));
        ptr = PREV_BLKP(ptr);
    }

    /* case 4 */ // 이전 블럭 최하위 bit 0(비할당), 다음 블럭 최하위 bit 0(비할당)이면, 이전 블럭/현재 블럭/다음 블럭 모두 병합한 뒤 새로운 bp return
    else { 
        size += GET_SIZE(HDRP(PREV_BLKP(ptr))) + GET_SIZE(FTRP(NEXT_BLKP(ptr)));
        PUT(HDRP(PREV_BLKP(ptr)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(ptr)), PACK(size, 0));
        ptr = PREV_BLKP(ptr);
    }
    next_ptr = ptr; // next fit을 쓰기 위해 저장해준다
    return ptr;
}


/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */ // 무조건 새거 넣고 다시 프리시키는 방식
// void *mm_realloc(void *ptr, size_t size) // malloc + free. 이전 포인터에서 다음 포인터로 값과 메모리 할당을 이동시키는데 그 과정에서 말록, 카피, 프리시킴.
// {
//     void *oldptr = ptr;
//     void *newptr;
//     size_t copySize;
    
//     newptr = mm_malloc(size);
//     if (newptr == NULL) { // 말록 실패하면 리턴 null해서 프로그램 종료시킴
//       return NULL;
//     }
//     copySize = *(size_t *)((char *)oldptr - WSIZE);
//     if (size < copySize) {
//       copySize = size;
//     }
//     memcpy(newptr, oldptr, copySize); // newptr를 oldptr에 copysize만큼 복사 (memcpy:내장함수)
//     mm_free(oldptr);
//     return newptr;
// }

void *mm_realloc(void *bp, size_t size) { /* 이미 할당한 공간의 크기를 바꿀 때 사용(재할당), 뒤에까지 다 free하는 방식 */
    size_t old_size = GET_SIZE(HDRP(bp));
    size_t new_size = size + (2 * WSIZE);   // 2*WSIZE는 헤더와 풋터

    // new_size가 old_size보다 작거나 같으면 기존 bp 그대로 사용
    if (new_size <= old_size) {
        return bp;
    }
    // new_size가 old_size보다 크면 사이즈 변경
    else {
        size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
        size_t current_size = old_size + GET_SIZE(HDRP(NEXT_BLKP(bp)));

        // next block이 가용상태(0)이고 old, next block의 사이즈 합이 new_size보다 크면 그냥 그거 바로 합쳐서 쓰기
        if (!next_alloc && current_size >= new_size) {
            PUT(HDRP(bp), PACK(current_size, 1));
            PUT(FTRP(bp), PACK(current_size, 1));
            return bp;
        }
        // 아니면 새로 block 만들어서 거기로 옮기기
        else {
            void *new_bp = mm_malloc(new_size);
            // place(new_bp, new_size);
            memcpy(new_bp, bp, new_size);  // 메모리의 특정한 부분으로부터 얼마까지의 부분을 다른 메모리 영역으로 복사해주는 함수
            // (old_bp로부터 new_size만큼의 문자를 new_bp로 복사해라!)
            mm_free(bp);
            return new_bp;
        }
    }
}


/* First fit search */

// /*
//  * mm-naive.c - The fastest, least memory-efficient malloc package.
//  * 
//  * In this naive approach, a block is allocated by simply incrementing
//  * the brk pointer.  A block is pure payload. There are no headers or
//  * footers.  Blocks are never coalesced or reused. Realloc is
//  * implemented directly using mm_malloc and mm_free.
//  *
//  * NOTE TO STUDENTS: Replace this header comment with your own header
//  * comment that gives a high level description of your solution.
//  */
// #include <stdio.h>
// #include <stdlib.h>
// #include <assert.h>
// #include <unistd.h>
// #include <string.h>

// #include "mm.h"
// #include "memlib.h"

// /*********************************************************
//  * NOTE TO STUDENTS: Before you do anything else, please
//  * provide your team information in the following struct.
//  ********************************************************/
// team_t team = {
//     /* Team name */
//     "week06-05",
//     /* First member's full name */
//     "Yerim",
//     /* First member's email address */
//     "sontt4266@naver.com",
//     /* Second member's full name (leave blank if none) */
//     "",
//     /* Second member's email address (leave blank if none) */
//     ""
// };

// /* single word (4) or double word (8) alignment */
// #define ALIGNMENT 8

// /* rounds up to the nearest multiple of ALIGNMENT */
// #define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7) // ptr에 7byte를 더한 위치에서 allocate bit를 제거
//                     // align으로 크기 맞춰줌 (1칸 뺌) & 비트마스크
//                     // 0x7(주소) = 7 = 111(2) // ~은 not. 전부 뒤집어져서 111 -> 000
//                     // 아무 숫자 15321341 111 & 000 -> 은 000이 되니까 값을 지워줄 수 있게 됨. 이 이후에 포인터 앞으로 다시 보냄


// #define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

// /* p.825 */
// /* Basic constants and macros */
// #define WSIZE       4           /* Word and header/footer zise (bytes) */
// #define DSIZE       8           /* Double word size (bytes) */
// #define CHUNKSIZE   (1<<10)     /* Extend heap by this amount (bytes) */ //초기 힙 사이즈 설정
//                 // '<<' : 비트쉬프트 : 1을 2진법으로 12칸 보내겠다 - 0이 12개 붙음 -> 1 -> 1000000000000

// #define OVERHEAD 8
// #define MAX(x, y) ((x) > (y)? (x) : (y))

// /* PAck a size and allocated bit into a word */ // 처음에 최하위 3bit를 떼었으니 malloc후 생긴 새로운 값을 묶음
// #define PACK(size, alloc)   ((size) | (alloc)) // size와 alloc의 값을 한 word로 묶고, 이를 이용해 h와 f에 쉽게 저장.
//                                 // '|' : or 연산자
// /* Read and write a word at address p */ 
// #define GET(p)      (*(unsigned int *)(p)) // 포인터 p가 가리키는 곳의 한 word 값을 읽어온다 
// #define PUT(p, val) (*(unsigned int *)(p) = (val)) // 포인터 p가 가리키는 곳의 한 word의 값에 val를 기록 
//                     // unsigned int > size_t로 바꾸기
// /* Read the size and allocated fields from address p */
// #define GET_SIZE(p)     (GET(p) & ~0x7) // 포인터 p가 가리키는 곳에서 한 word를 읽은 다음 하위 3bit를 버린다. 즉, header에서 block size를 읽는다.
// #define GET_ALLOC(p)    (GET(p) & 0x1) // 포인터 p가 가리키는 곳에서 한 word를 읽은 다음 최하위 1bit를 읽는다. 1할당, 0노할당

// /* Given block ptr bp, compute address of its geader and footer */
// #define HDRP(bp)        ((char *)(bp) - WSIZE) // 주어진 포인터 bp의 header(-4)의 주소를 계산 // bp : 페이로드가 시작되는 부분
// #define FTRP(bp)        ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE) // 주어진 포인터 bp의 footer 주소 계산
//                                     // GET_SIZE(4) - 8 : 헤더값이 포함된 size - 헤더, 풋터값(8)
//                     // (char *)(bp) : bp 포인터가 가리키는 블록의 주소를 얻어온다
//                     // 헤더에서 3비트빼면 getsize에서 블록 전체의 헤더뺀 사이즈를 얻음
//                     // bp : 페이로드의 시작 ptr. = 블록의 시작이 아님
//                     // 푸터는 헤더의 카피. 그래서 똑같이 4를 돌아가면 푸터의 시작점을 알 수 있음

// /* Given block ptr bp, compute address of next and previous blocks */
// #define NEXT_BLKP(bp)   ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE))) // 주어진 포인터 bp를 이용해서 다음 블록 주소 얻어옴
// #define PREV_BLKP(bp)   ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE))) // 이전 블록 주소 얻어옴
// // 빼주면 윗 블럭의 사이즈를 알 수 있다

// static void *heap_listp;
// static char *next_ptr;
// static void *extend_heap(size_t words);
// static void *coalesce(void *ptr);
// static void *find_fit(size_t a_size);
// static void place(void *bp, size_t a_size);

// /* 
//  * mm_init - initialize the malloc package.
//  */
// int mm_init(void)
// { // 할당기 : 초기화 완료 후, 어플리케이션으로부터 할당과 반환 요청을 받을 준비를 완료한다. 
//     /* Create the initial empty heap */
//     if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1) { // sbrk로 4워드(16바이트)할당 : 빈 가용 리스트 만들도록 초기화. 
//     // mem_sbrk 함수 돌리면 내가 넣은 인풋값만큼의 영역이 있는지 찾아보고 있으면 그 포인터주소를 heap_listp에 반환하고 아니면 -1 리턴하는 함수. 최소 16바이트인데 16바이트만큼 넣을 공간이 없으면 에러라서 조건문에 들어가서 -1 반환
//         return -1; 
//     }
    
//     PUT(heap_listp, 0);                         /* Alignment padding */ // 첫번째 워드 : 더블워드 경계로 정렬된 미사용 패딩워드
//     PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1)); /* Prologue header */ // 헤더 + 풋터로만 구성된 8바이트 할당 블록, 프롤로그 블록 - 초기화 과정에서 생성, 절대 반환X
//     PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1)); /* Prologue footer */ 
//     PUT(heap_listp + (3*WSIZE), PACK(0, 1));     /* Epilogue header */ // 힙 : 에필로그 블록으로 끝남, 헤더로만 구성된 크기가 0 으로 할당된 블록
//     heap_listp += (2*WSIZE); // 현재 위치를 나타내는 포인터. 2워드 뒤로 옮긴다


//     /* Extend the empty heap with a free block of CHUNKSIZE bytes */
//     if (extend_heap(CHUNKSIZE/WSIZE) == NULL) { // 힙을 CHUCKSIZE바이트로 확장, 초기 가용 블록 생성.
//         return -1;                              // Next fit을 이용할 경우, next_ptr를 heap_listp로 초기화한다.
//     }
//     return 0;
// }


// static void *extend_heap(size_t words) /* 새 가용 블록으로 힙을 확장하는 함수 */
// {
//     char *bp;
//     size_t size;

//     /* Allocate an even number of words to maintain alignment */
//     // 요청한 크기를 인접 2워드의 배수로 반올림, 그 후에 sbrk로 메모리시스템으로부터 추가적인 힙 공간 요청
//     size = (words % 2) ? (words+1) * WSIZE : words * WSIZE; // 나머지가 0 : false, 그 외 : true -> 8의배수로 맞춰짐
//     if ((long)(bp = mem_sbrk(size)) == -1) { // long : 정수타입 8바이트 (int 4바이트) // long 빼고 if ((bp = mem_sbrk(size)) == (void *)-1) 으로 써도 됨 // 여기서 mem_sbrk가 size요청받은 만큼 힙을 확장, H, F, P다 생김
//         return NULL;
//     }

//     /* Initialize(초기화) free block header/footer and the epilogue header */
//     PUT(HDRP(bp), PACK(size, 0));           /* Free block header */ // 한 칸 뒤로가면서 해당 칸 0(free)시키면서 그 자리를 H로 풋 됨.
//     PUT(FTRP(bp), PACK(size, 0));           /* Free block footer */ // 
//     // HDRP에 헤더값이 들어있으니 헤더값을 알면 그 블록의 사이즈, 정보를 다 아니까 GET_SIZE로 H, F, P값 다 불러옴 프리 블록의 bp는 힙의 끝에 있음. 거기서 -8한 부분을 푸터로 바꿔준다
//     PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));   /* New epilogue header */

//     /* Coalesce if the previous block was free */
//     return coalesce(bp);
// }


// /* 
//  * mm_malloc - Allocate a block by incrementing the brk pointer.
//  *     Always allocate a block whose size is a multiple of the alignment.
//  */
// void *mm_malloc(size_t size) // malloc : size 바이트의 메모리 블록을 요청
// { // 원래 써있던 코드
//     // int newsize = ALIGN(size + SIZE_T_SIZE);
//     // void *p = mem_sbrk(newsize);
//     // if (p == (void *)-1) {
// 	// return NULL;
//     // }
//     // else {
//     //     *(size_t *)p = size;
//     //     return (void *)((char *)p + SIZE_T_SIZE);
//     // }

//     // 여기부터 교재 P.828
//     size_t asize;       /* Adjusted block size */
//     size_t extendsize;  /* Amount to extend heap if no fit */
//     char *bp;

//     /* Ignore spurious requests */
//     if (size == 0) {
//         return NULL;
//     }

//     /* Adjust block size to include overhead and alignment reqs. */
//     /* 최소 16바이트 크기의 블록 구성. 8바이트 for 정렬 조건 만족 위해, 추가 8바이트 for 헤더, 풋터 오버헤드를 위해 */
//     if (size <= DSIZE) {
//         asize = 2*DSIZE; // adjust size : 조정된 사이즈. 2*8 = 16 , 8보다 작은 요청값은 다 16으로 만든다
//     }
//     else { // 8바이트 넘는 요청 : 오버헤드 바이트 내에 더해주고, 인접 8의 배수로 반올림
//         asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE); 
//     }
//     /* Search the free lish for a fit */ // find_fit으로 적절한 가용블록을 가용리스트에서 검색
//     if ((bp = find_fit(asize)) != NULL) { 
//         // 맞는 블록 찾으면 - 할당기 : place로 요청 블록 배치, 옵션으로 초과부분 분할, 새 할당 블록 리턴(반환)
//         place(bp, asize); // put해서 bp를 헤더에 asize만큼 넣어준다(할당해준다) 
//         return bp;
//     }

//     /* No fit found. Get more memory and place the block */ 
//     // 못찾으면 : extend_heap으로 힙을 새 가용 블록으로 확장(메모리 공간 더 할당), 요청 블록을 이 새 가용 블록에 배치
//     extendsize = MAX(asize, CHUNKSIZE);
//     if ((bp = extend_heap(extendsize/WSIZE)) == NULL) {
//         return NULL;
//     }
//     place(bp, asize); // 필요하면 블록 분할
//     return bp;
// }

// static void *find_fit(size_t a_size) { 
// //     /* first fit search */
// //     void *bp;
// //     // for (bp 여기부터, n>0까지; 다음블록으로 이동)
// //     for (bp = (char *)heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
// //         if (!GET_ALLOC(HDRP(bp)) && (a_size <= GET_SIZE(HDRP(bp)))) {
// //             return bp;
// //         }
// //     }
// //     return NULL; /* No fit */ // 끝가지 돌았는데 없을 때 NULL값 리턴
// // }
// }

// static void place(void *bp, size_t a_size) {
// /* 요청 블록을 가용 블록 시작 부분에 배치하여, 나머지 부분 크기가 최소 블록 크기와 같거나 큰 경우에만 분할 */
// /* 블록을 배치한 후에 나머지 부분의 크기가 최소 블록 크기와 같거나 크다면, 블록을 분할.
//     다음 블록으로 이동하기 전에 새롭게 할당한 블록을 배치해야 한다 */
//     size_t c_size = GET_SIZE(HDRP(bp)); // current_size

//     // 배치 후에 이 블록의 나머지가 최소 블록의 크기와 같거나 크다면, 진행해서 블록을 분할해야 한다.
//     if ((c_size - a_size) >= (2 * (DSIZE))) { // 최소 16보다 큰 경우에 대해서. c가 현재 블록의 크기, a가 우리가 넣으려는 크기. 둘 빼서 들어갈 수 있는지. 16보다 큰 경우
//         // 요청 용량 만큼 새롭게 할당한 블록 배치
//         PUT(HDRP(bp), PACK(a_size, 1)); // 16보다 커서 넥스트블록으로 넘어갈 경우, 앞 블록은 이미 찾으니까 써야하고
//         PUT(FTRP(bp), PACK(a_size, 1)); // 뒤에 블록에 다음 블록으로 넘어가서 또 할당을 한다는 의미..
//         bp = NEXT_BLKP(bp); // 다음 블록으로 이동
//         // 남은 블록에 header, footer 배치
//         PUT(HDRP(bp), PACK(c_size - a_size, 0));
//         PUT(FTRP(bp), PACK(c_size - a_size, 0));
//     }
//     else { // csize와 aszie 차이가 네 칸(16byte)보다 작다면 해당 블록 통째로 사용한다.(전체를 할당)
//         PUT(HDRP(bp), PACK(c_size, 1));
//         PUT(FTRP(bp), PACK(c_size, 1));
//     }
// }

// /*
//  * mm_free - Freeing a block does nothing.
//  */ // 이전에 할당한 블록을 free함수를 호출해서 반환한다 : 요청 블록을 반환하고, 인접 가용 블록들을 coalesce로 통합한다.
// void mm_free(void *ptr) 
// {
//     if(!ptr) return; // 잘못된 free요청일 경우 함수 종료, 이전 프로시져로 return

//     size_t size = GET_SIZE(HDRP(ptr)); // ptr의 헤더에서 block size 읽어 옴
    
//     // 실제로 데이터를 지우는 게 아니라 header와 footer의 최하위 1비트(할상된 상태)만을 수정
//     PUT(HDRP(ptr), PACK(size, 0)); // ptr의 header에 block size와 alloc = 0을 저장
//     PUT(FTRP(ptr), PACK(size, 0)); // ptr의 footer에 block size와 alloc = 0을 저장
//     coalesce(ptr); // 주위에 빈 블럭이 있을 시 병합
// }

// static void *coalesce(void *ptr)
// {
//     size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(ptr))); // 이전 블럭 할당 여부; no=0, yes=1
//     size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(ptr))); // 다음 ~
//     size_t size = GET_SIZE(HDRP(ptr)); // 현재 블럭의 size
    
//     /* case 1 */ // 이전 블럭, 다음 블럭 최하위 bit 둘 다 1 할당이면, 블럭 병합 없이 bp return
//     if (prev_alloc && next_alloc) {
//         return ptr;
//     }

//     /* case 2 */ // 이전 블럭 최하위 bit 1(할당)이고, 다음 블럭 최하위 bit 0(비할당)이면, 다음 블럭과 병합한 뒤 bp return
//     else if (prev_alloc && !next_alloc) {
//         size += GET_SIZE(HDRP(NEXT_BLKP(ptr)));
//         PUT(HDRP(ptr), PACK(size, 0)); // alloc을 0으로 -> 할당으로 바꿈
//         PUT(FTRP(ptr), PACK(size, 0));
//     }

//     /* case 3 */ // 이전 블럭 최하위 bit 0(비할당), 다음 블럭 최하위 bit 1(할당)이면, 이전 블럭과 병합한 뒤 새로운 bp return
//     else if (!prev_alloc && next_alloc) {
//         size += GET_SIZE(HDRP(PREV_BLKP(ptr)));
//         PUT(FTRP(ptr), PACK(size, 0));
//         PUT(HDRP(PREV_BLKP(ptr)), PACK(size, 0));
//         ptr = PREV_BLKP(ptr);
//     }

//     /* case 4 */ // 이전 블럭 최하위 bit 0(비할당), 다음 블럭 최하위 bit 0(비할당)이면, 이전 블럭/현재 블럭/다음 블럭 모두 병합한 뒤 새로운 bp return
//     else { 
//         size += GET_SIZE(HDRP(PREV_BLKP(ptr))) + GET_SIZE(FTRP(NEXT_BLKP(ptr)));
//         PUT(HDRP(PREV_BLKP(ptr)), PACK(size, 0));
//         PUT(FTRP(NEXT_BLKP(ptr)), PACK(size, 0));
//         ptr = PREV_BLKP(ptr);
//     }
//     return ptr;
// }


// /*
//  * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
//  */ // 무조건 새거 넣고 다시 프리시키는 방식
// // void *mm_realloc(void *ptr, size_t size) // malloc + free. 이전 포인터에서 다음 포인터로 값과 메모리 할당을 이동시키는데 그 과정에서 말록, 카피, 프리시킴.
// // {
// //     void *oldptr = ptr;
// //     void *newptr;
// //     size_t copySize;
    
// //     newptr = mm_malloc(size);
// //     if (newptr == NULL) { // 말록 실패하면 리턴 null해서 프로그램 종료시킴
// //       return NULL;
// //     }
// //     copySize = *(size_t *)((char *)oldptr - WSIZE);
// //     if (size < copySize) {
// //       copySize = size;
// //     }
// //     memcpy(newptr, oldptr, copySize); // newptr를 oldptr에 copysize만큼 복사 (memcpy:내장함수)
// //     mm_free(oldptr);
// //     return newptr;
// // }

// void *mm_realloc(void *bp, size_t size) { /* 뒤에까지 다 free하는 방식 */
//     size_t old_size = GET_SIZE(HDRP(bp));
//     size_t new_size = size + (2 * WSIZE);   // 2*WSIZE는 헤더와 풋터

//     // new_size가 old_size보다 작거나 같으면 기존 bp 그대로 사용
//     if (new_size <= old_size) {
//         return bp;
//     }
//     // new_size가 old_size보다 크면 사이즈 변경
//     else {
//         size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
//         size_t current_size = old_size + GET_SIZE(HDRP(NEXT_BLKP(bp)));

//         // next block이 가용상태이고 old, next block의 사이즈 합이 new_size보다 크면 그냥 그거 바로 합쳐서 쓰기
//         if (!next_alloc && current_size >= new_size) {
//             PUT(HDRP(bp), PACK(current_size, 1));
//             PUT(FTRP(bp), PACK(current_size, 1));
//             return bp;
//         }
//         // 아니면 새로 block 만들어서 거기로 옮기기
//         else {
//             void *new_bp = mm_malloc(new_size);
//             // place(new_bp, new_size);
//             memcpy(new_bp, bp, new_size);  // 메모리의 특정한 부분으로부터 얼마까지의 부분을 다른 메모리 영역으로 복사해주는 함수(old_bp로부터 new_size만큼의 문자를 new_bp로 복사해라!)
//             mm_free(bp);
//             return new_bp;
//         }
//     }
// }

// // int main() {
// //     char *temp;
// //     temp = malloc(9);
// // }



