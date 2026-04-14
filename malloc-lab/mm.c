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

// #define DEBUG

#ifdef DEBUG
#define dbg_printf(...) printf(__VA_ARGS__)
#else
#define dbg_printf(...)
#endif
/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "ateam",
    /* First member's full name */
    "Harry Bovik",
    /* First member's email address */
    "bovik@cs.cmu.edu",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

// size를 8바이트 배수로 올림하는 매크로
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)

// size_t의 크기를 8바이트 정렬 기준으로 맞춘 값
#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

#define WSIZE SIZE_T_SIZE       // 4
#define DSIZE (2 * SIZE_T_SIZE) // 8
#define CHUNKSIZE (1 << 12)

// 둘 중 큰 값 반환
#define MAX(x, y) ((x) > (y) ? (x) : (y))

#define PACK(size, alloc) ((size) | (alloc))

// 주소 p에 있는 4바이트 값을 읽는다
// GET(p) == 0x19
#define GET(p) (*(unsigned int *)(p))

// 주소 p에 val을 4바이트로 저장한다
// ex) PUT(p, 0x19) -> p위치 header에 0x19가 써진다.
#define PUT(p, val) (*(unsigned int *)(p) = (val)) // 주소 p를 unsigned int를 가리키는 포인터로 보겠다

// header/footer 값에서 size만 추출한다
// GET_SIZE(p) = 25 & ~0x7 = 24
#define GET_SIZE(p) (GET(p) & ~0X7)

// header/footer 값에서 할당 여부 bit만 추출한다
// GET_ALLOC(p) = 25 & 0x1 = 1
#define GET_ALLOC(p) (GET(p) & 0x1)

// payload 포인터 bp로부터 header 주소를 구한다
// ex) HDRP(bp) = 0x1008 - 4 = 0x1004
#define HDRP(bp) ((char *)(bp) - WSIZE)

// payload 포인터 bp로부터 footer 주소를 구한다
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

// 현재 블록의 payload 포인터 bp에서 다음 블록의 payload 포인터를 구한다
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))

// 현재 블록의 payload 포인터 bp에서 이전 블록의 payload 포인터를 구한다.
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

/*
 * mm_init - initialize the malloc package.
 */

// 힙의 주소
static char *heap_listp;

// 다음에도 기억할 next_fit 주소
static void *nextAddress = NULL;

// 현재 free block bp를 기준으로, 앞뒤 free 블록과 합쳐서 더 큰 free block으로 만드는 함수
static void *coalesce(void *bp)
{
    // 이전 블록의 footer를 보고 할당 상태인지 확인
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));

    // 다음 블록의 header를 보고 할당 상태인지 확인
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));

    // 현재 블록 크기 읽기
    size_t size = GET_SIZE(HDRP(bp));

    // 앞도 사용중, 뒤도 사용중
    if (prev_alloc && next_alloc)
    {
        return bp;
    }

    // 앞은 사용중, 뒤는 free
    else if (prev_alloc && !next_alloc)
    {
        // 현재 크기 + 다음 블록크기
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));

        // 헤더 size 교체
        PUT(HDRP(bp), PACK(size, 0));
        // footer size 교체
        PUT(FTRP(bp), PACK(size, 0));

        // if (nextAddress == NEXT_BLKP(bp) || nextAddress == bp)
        //     nextAddress = bp;
    }

    // 앞은 free, 뒤는 사용 중
    else if (!prev_alloc && next_alloc)
    {
        // 현재 사이즈에 이전 사이즈 더해준다
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));

        // 앞에거랑 합쳐졌으므로 현재 뒤에거 사이즈 변경
        PUT(FTRP(bp), PACK(size, 0));

        // 이전 블록의 헤더 주소에 현재 사이즈 변경
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));

        // 주소를 이전 블록의 payload 주소로 바꾼다
        bp = PREV_BLKP(bp);

        // if (nextAddress == PREV_BLKP(bp) || nextAddress > bp)
        //     nextAddress = bp;
    }

    // 둘다 비었을 때
    else
    {
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);

        // if(nextAddress >= bp)
        // {
        //     nextAddress = bp;
        // }
    }
    dbg_printf("병합됨         =>  header: %p(%ld bytes)   size:%d bytes\n", HDRP(bp), HDRP(bp) - (char *)heap_listp, (int)(size));
    
    nextAddress = bp;  // 병합된 블록으로 nextAddress 업데이트
    return bp;
}

// 힙 공간 부족할 때 힙을 뒤로 더 늘려서 새로운 free block을 만드는 함수
static void *extend_heap(size_t words) // 1024
{
    // 새로 늘린 힙 공간에서 새 free block의 payload를 가리키는 포인터
    char *bp;

    // 실제로 얼마나 늘릴지 저장할 변수
    size_t size;

    // words가 홀수면 1워드 더해서 짝수로 만들고, 짝수면 그대로 쓴다는 뜻 => 블록 크기를 8바이트 배수로 맞추려고
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;

    // 힙 끝에서 size만큼 새 공간을 달라고 요청하는 것
    if ((long)(bp = mem_sbrk(size)) == -1)
    {
        return NULL;
    } // bp에는 그 새 공간의 시작주소 담긴다

    // 새 free block의 헤더를 만든다는 뜻(에필로그 헤더 자리이다)
    // bp의 헤더 주소에 이 값을 넣는다
    PUT(HDRP(bp), PACK(size, 0));

    // bp의 footer주소에 이 값을 넣는다
    PUT(FTRP(bp), PACK(size, 0));

    // 새 free block 뒤에 새 epilogue header를 만드는 것
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));

    // 앞 블록도 free라면
    // 처음 extend_heap의 coalesce는 아무것도 안한다
    return coalesce(bp);
}

// 빈 곳 찾으면 place로 배치
static void place(void *bp, size_t allocated_size)
{
    size_t curr_size = GET_SIZE(HDRP(bp));

    // Case 1. 남는 부분이 최소 블록 크기(16 bytes) 이상일 때 -> 블록 분할

    if ((curr_size - allocated_size) >= (2 * DSIZE))
    {
        PUT(HDRP(bp), PACK(allocated_size, 1)); // 헤더, 사이즈랑 할당 바꿔준다
        PUT(FTRP(bp), PACK(allocated_size, 1)); // 푸터, 사이즈랑 할당 바꿔준다
        bp = NEXT_BLKP(bp);                     // payload 주소로

        nextAddress = bp;

        PUT(HDRP(bp), PACK(curr_size - allocated_size, 0)); // 새로운 헤더 사이즈 생성
        PUT(FTRP(bp), PACK(curr_size - allocated_size, 0)); // 에필로그 헤더에 남은 사이즈
    }
    // Case 2. 남는 부분이 최소 블록 크기(16 bytes) 미만일 때 -> 블록 분할 필요 X

    else
    {
        PUT(HDRP(bp), PACK(curr_size, 1));
        PUT(FTRP(bp), PACK(curr_size, 1));
    }
}

// first fit 버전
// free 블록 찾기
//  static void *find_fit(size_t asize)
//  {
//      //현재 보고 있는 블록의 payload 주소
//      void *bp;

//     // heap_listp: 힙의 시작쪽을 가리키는 포인터;
//     //GET_SIZE(HDRP(bp)) : 현재 블록 크기 -> 맨 끝의 에필로그 헤더의 크기는 0이기 때문에 그 전까지 계속 순회하라는 뜻
//     //NEXT_BLKP(bp) : 현재 블록 크기만큼 앞으로 가서 다음 블록의 payload 주소를 구한다
//     for(bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp))
//     {
//         // GET_ALLOC(HDRP(bp)) -> 헤더에서 할당여부만 꺼내는 코드에서 할당되었는지 안되었는지 확인 , 0이면 free라는 뜻
//         // 현재 free block size가 내가 할당하고 싶은 사이즈보다 큰가
//         if(!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp))))
//         {
//             return bp; // payload 주소를 준다
//         }
//     }

//     // 빈 곳이 없으면 NULL 반환
//     return NULL;
// }

// next fit 버전
static void *find_fit(size_t asize)
{
    void *bp;


    for (bp = nextAddress; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp))
    {
        // GET_ALLOC(HDRP(bp)) -> 헤더에서 할당여부만 꺼내는 코드에서 할당되었는지 안되었는지 확인 , 0이면 free라는 뜻
        // 현재 free block size가 내가 할당하고 싶은 사이즈보다 큰가
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp))))
        {
            nextAddress = bp;
            return bp; // payload 주소를 준다
        }
    }

    for(bp = heap_listp; GET_SIZE(HDRP(bp)) > 0 && bp != nextAddress; bp = NEXT_BLKP(bp))
    {
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp))))
        {
            nextAddress = bp;
            return bp; // payload 주소를 준다
        }
    }
    return NULL;
}


int mm_init(void)
{
    //[패딩(0)] [프롤로그 헤더(8/1)] [프롤로그 푸터(8/1)] [에필로그 헤더(0/1)] 순서로 초기화

    void* init_bp;

    if ((heap_listp = mem_sbrk(DSIZE * 2)) == (void *)-1)
    {
        return -1;
    }

    PUT(heap_listp, 0);
    PUT(heap_listp + WSIZE, PACK(DSIZE, 1)); //
    PUT(heap_listp + WSIZE * 2, PACK(DSIZE, 1));
    PUT(heap_listp + WSIZE * 3, PACK(0, 1));

    heap_listp += DSIZE;

    init_bp = extend_heap(CHUNKSIZE / WSIZE);
    // free 블록 만든다
    if (init_bp == NULL) // 1024
    {
        return -1;
    }

    nextAddress = init_bp; // 테스트 1하고 테스트 2할때 이 값이 NULL 이어야 한다

    dbg_printf("\nmm_init:  heap_strt: %p (0 bytes) \n\n", heap_listp);

    return 0;
}

/*
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    size_t asize;
    size_t extendsize;
    char *bp;
    // dbg_printf("mm_malloc 실행 => %8d %8d", asize, (int)size);

    if (size == 0)
    {
        return NULL;
    }

    // 할당하려고 하는 size가 8보다 작으면
    if (size <= DSIZE)
    {
        // 16바이트 준다 -> 이유 : payload가 8바이트면,  헤더 : 4바이트, 푸터 : 4바이트
        asize = 2 * DSIZE;
    }
    // 할당하려고 하는 size가 8보다 크면
    else
    {
        // 8의 배수가 되게 하려고 DSIZE(헤더 + 푸터 공간 8바이트) + 올림용 7바이트
        // 주소 정렬이 유지된다
        asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);
    }

    // 빈 블록 찾기
    if ((bp = find_fit(asize)) != NULL)
    {

        place(bp, asize);
        dbg_printf("  =>  내부 찾음   header: %p (%ld bytes)\n", HDRP(bp), (char *)HDRP(bp) - (char *)heap_listp);
        return bp;
    }

    // 빈 블록 없는 경우
    // 힙 확장한다
    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize / WSIZE)) == NULL)
    {
        return NULL;
    }

    // 새 힙 영역에 블록 배치
    place(bp, asize);
    return bp;
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp));

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));

    dbg_printf("메모리 해제    =>  header: %8p   size: %d bytes\n", HDRP(bp), (int)(size));

    coalesce(bp);
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
// 기존에 가지고 있던 메모리 블록의 크기를 바꾸고 싶을 때 쓰는 함수
// 원래 10바이트 짜리 배열을 만들었는데 나중에 20바이트가 필요해질때 쓴다
// 흐름 : 새 크기로 새메모리 할당 -> 예전 데이터 복사 -> 옛 메모리 free -> 새 주소 반환
void *mm_realloc(void *ptr, size_t size)
{
    // ex) char *p = mm_malloc(10) -> 사용자가 10바이트 요청
    void *oldptr = ptr;
    void *newptr;
    size_t copySize;

    // 새 크기만큼 새 공간을 받는다.
    newptr = mm_malloc(size);
    if (newptr == NULL)
        return NULL;

    // oldptr : payload 주소
    copySize = GET_SIZE(HDRP(oldptr)) - DSIZE; //*(size_t *)((char *)oldptr - SIZE_T_SIZE);

    // 새블록이 작으면 기존 크기와 비교해서 더 작은값
    // ex) old size = 10, new size = 6 -> 앞의 6바이트만 복사한다, 뒤 4바이트는 잘린다
    if (size < copySize)
        copySize = size;

    // oldptr 데이터 newptr로 copySize 바이트만큼 복사하는것
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;
}
