#include <stdio.h>
#include <string.h>
#include <stdlib.h>

#include "./bigint/bigint.h"


#define versionNumber "8"
#define versionNumberAsInt  8


/*
 * VM Instructions start
 */
#define HALT 0
#define PUSHC 1
#define ADD 2
#define SUB 3
#define MUL 4
#define DIV 5
#define MOD 6

#define RDINT 7
#define WRINT 8
#define RDCHR 9
#define WRCHR 10

#define PUSHG 11
#define POPG 12

#define ASF 13
#define RSF 14
#define PUSHL 15
#define POPL 16

#define EQ 17
#define NE 18
#define LT 19
#define LE 20
#define GT 21
#define GE 22

#define JMP 23
#define BRF 24
#define BRT 25

#define CALL 26
#define RET 27
#define DROP 28
#define PUSHR 29
#define POPR 30

#define DUP 31

#define NEW 32
#define GETF 33
#define PUTF 34

#define NEWA 35
#define GETFA 36
#define PUTFA 37

#define GETSZ 38
#define PUSHN 39
#define REFEQ 40
#define REFNE 41

#define MSB (1<<(8*sizeof(unsigned int)-1))
#define MBHB (1<<(8*sizeof(unsigned int)-2))

#define IS_PRIMITIV(objRef) (((objRef)->size&MSB)==0)
#define IS_BROKENHEART(objRef)  (((objRef)->size&MBHB)!=0)

#define GET_FORWARD_OFFSET(objRef)  ((objRef)->size&~((MSB) | (MBHB)))
#define GET_SIZE(objRef)    ((objRef)->size& ~((MSB) | (MBHB)))
#define GET_REFS(objRef)    ((ObjRef*)(objRef)->data)

#define KIB 1024

/*
 * Macros start
 * */
#define INSTRUCTION_SHIFT 24
#define INSTRUCTION(x) ((x)&0xFF000000)
#define IMMEDIATE(x) ((x) &0x00FFFFFF)
#define SING_EXTEND(x) ((x) & 0x00800000 ? (x) | 0xFF000000: (x))
/*
 * Macros end
 * */

/*
 * Stack definition
 * */
void exec(unsigned int);

void printInst(unsigned int);

void debugMode(void);

int runDebug(void);

int askDebugChoice(unsigned int);

int compareStrings(char *, char *);

void printStack(void);

void printData(void);

void printCode(void);

void setBreakpoint(char *);

int getNumberFromString(char, int);

void gcPurge(void);

void initGcStats(void);

void gcStats(void);

ObjRef newComObject(int);

ObjRef copyObjToFreeMem(ObjRef);

void* malloc_heap(int);

ObjRef relocate(ObjRef);

void copy_root_objects(void);

void flip_memory();

void collect_Garbage();

void scan_Root_Objects(void);

int static_var_count;
int pc;
unsigned int *instruction;
int instr_count;
int breakPoint;
ObjRef returnRegister;
BIP bip;
ObjRef staticData_comp;
int relocBytes;
int relocCount;
int livingObjectsCount;
int livingObjectsBytes;
int freeSizeInBytes;
int gc_Stats_Flag;
int gc_Purge_Flag;
int gc_Started_Flag;

typedef struct Heap{
    char *source;
    char *target;
    int heapSize;
    char *currentFreeTarget;
}Heap;
struct Heap heap;

void initHeap(int heapSize){
    heap.heapSize = (heapSize*KIB)/2;
    heap.source = malloc(heap.heapSize);
    heap.target = malloc(heap.heapSize);
    heap.currentFreeTarget = heap.target;
}

typedef struct StackSlot{
    int isObjRef;
    union {
        ObjRef objRef;
        int number;
    } u;
} StackSlot;

static const struct StackSlot emptySlot;

typedef struct Stack{
    StackSlot *slots;
    int sp;
    int fp;
    int stackSize;
} Stack;
struct Stack;


struct Stack stack;

void initStack(int stackSize) {
    stack.slots = malloc(stackSize * 1024);
    stack.fp = 0;
    stack.sp = 0;
    stack.stackSize = (stackSize*1024) / sizeof(StackSlot);
}

void push_number(int value) {
    stack.slots[stack.sp].u.number = value;
    stack.slots[stack.sp].isObjRef = 0;
    ++stack.sp;
}

void push_reference(ObjRef ref) {
    stack.slots[stack.sp].u.objRef = ref;
    stack.slots[stack.sp].isObjRef = 1;
    ++stack.sp;
}

int pop_number(void) {
    --stack.sp;
    if (stack.slots[stack.sp].isObjRef) {
        fatalError("Error: unexpected Object");
    }
    return stack.slots[stack.sp].u.number;
}

ObjRef pop_reference(void) {
    --stack.sp;
    if (!stack.slots[stack.sp].isObjRef) {
        fatalError("Error: unexpected Number");
    }
    return stack.slots[stack.sp].u.objRef;
}

void popg(int value) {
    GET_REFS(staticData_comp)[value] = pop_reference();
}

void pushg(int value) {
    push_reference(GET_REFS(staticData_comp)[value]);
}

void asf(int elem) {
    int i;
    push_number(stack.fp);
    stack.fp = stack.sp;
    stack.sp = stack.sp + elem;
    for ( i = stack.fp; i <stack.sp ; ++i) {
        stack.slots[stack.sp].u.objRef = NULL;
        stack.slots[stack.sp].isObjRef = 1;
    }
}

void rsf(void) {
    stack.sp = stack.fp;
    stack.fp = pop_number();
}

void pushl(int range) {
    if (!stack.slots[stack.fp + range].isObjRef) {
        fatalError("Error: unexpected Number");
    }
    push_reference(stack.slots[stack.fp + range].u.objRef);
}

void popl(int range) {
    ObjRef obj = pop_reference();
    stack.slots[stack.fp + range].u.objRef = obj;
    stack.slots[stack.fp + range].isObjRef = 1;
}


void interpret(void) {
    unsigned int ir;
    pc = 0;
    while (HALT != (ir = *(instruction + pc))) {
        pc = pc + 1;
        exec(ir);
    }
}

int main(int argc, char *argv[]) {

    int i; /*Loop Index*/
    char *arguments[] = {"--version", "--help", "--debug", "--stack", "--heap" ,"--gcpurge", "--gcstats"};
    char *version[] = {versionNumber};
    int format_Verification = 0x46424a4e;
    char *file_Name;
    FILE *fp;
    int debug_Mode_Flag = 0;
    int format;
    int version_Number;
    int file_Found = 0;
    int stack_Count_Elements = 64;
    int heap_Count_Elements = 8192;
    gc_Stats_Flag = 0;
    gc_Purge_Flag = 0;
    gc_Started_Flag = 0;

    if (argc == 0) {
        fatalError("Error: no code file specified");
    }
    for (i = 1; i < argc; ++i) {
        if ((strcmp(argv[i], arguments[0])) == 0) {
            printf("Ninja Virtual Machine version: %s\n", *version);
        } else if ((strcmp(argv[i], arguments[1])) == 0) {
            printf("Usage: ./VM_1_3.c [options] <code file>");
            printf("Options:\n");
            printf("  --debug\tstart virtual machine in debug mode\n");
            printf("  --help\tshows help\n");
            printf("  --version\tshows program version\n");
        } else if ((strcmp(argv[i], arguments[2])) == 0) {
            debug_Mode_Flag = 1;
        } else if((strcmp(argv[i], arguments[3]) == 0)){
            if(argv[i+1]!= NULL){
                if(strstr(argv[i+1], "--") != NULL){
                    continue;
                }
                stack_Count_Elements = atoi(argv[i+1]);
                if(stack_Count_Elements == 0){
                    printf("invalid stackSize: using default n = 64");
                    stack_Count_Elements = 64;
                }
                i++;
            }
        } else if((strcmp(argv[i], arguments[4]) == 0)){
            if(argv[i+1]!= NULL){
                if(strstr(argv[i+1], "--") != NULL){
                    continue;
                }
                heap_Count_Elements = atoi(argv[i+1]);
                if(heap_Count_Elements == 0){
                    printf("invalid heapsize: using default n = 8192");
                    heap_Count_Elements = 8192;
                }
                i++;
            }
        } else if((strcmp(argv[i], arguments[5]) == 0)){
            gc_Purge_Flag = 1;
        } else if((strcmp(argv[i], arguments[6]) == 0)){
            gc_Stats_Flag = 1;
        } else if (strstr(argv[i], ".bin") != NULL) {
            file_Name = argv[i];
            file_Found = 1;
        } else {
            printf("Error: unknown option %s, try '--help'\n", argv[i]);
            exit(99);
        }
    }
    if (file_Found == 0) {
        fatalError("Error: no code file specified");
    }


    initStack(stack_Count_Elements);
    initHeap(heap_Count_Elements);

    fp = fopen(file_Name, "r");
    if (fp == NULL) {
        printf("Error: cannot open code file '%s'\n", file_Name);
        exit(99);
    }

    fread(&format, 4, 1, fp);
    if (format_Verification != format) {
        printf("Wrong Format!\n");
        exit(99);
    }

    fread(&version_Number, 4, 1, fp);
    if (version_Number != versionNumberAsInt) {
        printf("Wrong Version\n");
        exit(99);
    }

    fread(&instr_count, 4, 1, fp);
    instruction = (unsigned int *) malloc((size_t) instr_count * sizeof(unsigned int));


    fread(&static_var_count, 4, 1, fp);

    staticData_comp = newComObject(static_var_count);
    for (i = 0; i <static_var_count ; ++i) {
        GET_REFS(staticData_comp)[i] = NULL;
    }


    fread(instruction, sizeof(unsigned int), (size_t) instr_count, fp);

    if (debug_Mode_Flag == 1) {
        printf("DEBUG: file\t:\t'%s'\n"
                       "code\t:\t%d instructions\n"
                       "data\t:\t%d objects\n"
                       "stack\t:\t%d slots\n"
                       "heap\t:\t%d * %d\n", file_Name, instr_count, static_var_count, stack_Count_Elements*64,2,heap.heapSize);
    }
    printf("Ninja Virtual Machine started\n");
    if (debug_Mode_Flag == 1) {
        debugMode();
    } else {
        interpret();
        if(gc_Started_Flag == 0){
            gcStats();
        }
    }

    printf("Ninja Virtual Machine stopped\n");
    return 0;
}

void printInst(unsigned int ir) {
    unsigned int inst;
    int immediate;


    inst = INSTRUCTION(ir);
    immediate = SING_EXTEND(IMMEDIATE(ir));
    inst = inst >> INSTRUCTION_SHIFT;

    printf("%04d:\t", pc - 1);
    switch (inst) {
        case (HALT):
            printf("halt\n");
            break;
        case (PUSHC):
            printf("push:\t%d\n", immediate);
            break;
        case (ADD):
            printf("add\n");
            break;
        case (SUB):
            printf("sub\n");
            break;
        case (MUL):
            printf("mul\n");
            break;
        case (DIV):
            printf("div\n");
            break;
        case (MOD):
            printf("mod\n");
            break;
        case (RDINT):
            printf("rdint\n");
            break;
        case (WRINT):
            printf("wrint\n");
            break;
        case (RDCHR):
            printf("rdchr\n");
            break;
        case (WRCHR):
            printf("wrchr\n");
            break;
        case (PUSHG):
            printf("pusg:\t%d\n", immediate);
            break;
        case (POPG):
            printf("popg:\t%d\n", immediate);
            break;
        case (ASF):
            printf("asf:\t%d\n", immediate);
            break;
        case (RSF):
            printf("rsf\t\n");
            break;
        case (PUSHL):
            printf("pushl:\t%d\n", immediate);
            break;
        case (POPL):
            printf("popl:\t%d\n", immediate);
            break;
        case (EQ):
            printf("eq\n");
            break;
        case (NE):
            printf("ne\n");

            break;
        case (LT):
            printf("lt\n");
            break;
        case (LE):
            printf("le\n");
            break;
        case (GT):
            printf("gt\n");
            break;
        case (GE):
            printf("ge\n");
            break;
        case (JMP):
            break;
        case (BRF):
            printf("brf:\t%d\n", immediate);
            break;
        case (BRT):
            printf("brt:\t%d\n", immediate);
            break;
        case (CALL):
            printf("call:\t%d\n", immediate);
            break;
        case (RET):
            printf("ret\n");
            break;
        case (DROP):
            printf("drop:\t%d\n", immediate);
            break;
        case (PUSHR):
            printf("pushr\n");
            break;
        case (POPR):
            printf("popr\n");
            break;
        case (DUP):
            printf("dup\n");
            break;
        case(NEW):
            printf("new: \t%d\n", immediate);
            break;
        case(GETF):
            printf("getf: \t%d\n", immediate);
            break;
        case(PUTF):
            printf("putf: \t%d\n", immediate);
            break;
        case(NEWA):
            printf("newa\n");
            break;
        case (GETFA):
            printf("getfa\n");
            break;
        case (PUTFA):
            printf("putfa\n");
            break;
        case (GETSZ):
            printf("getsz\n");
            break;
        case (PUSHN):
            printf("pushn\n");
            break;
        case (REFEQ):
            printf("refeq\n");
            break;
        case (REFNE):
            printf("refne\n");
            break;
        default:
            fatalError("Error: unknown Instruction");
    }
}

void exec(unsigned int ir) {
    unsigned int inst;
    int immediate;
    ObjRef operand_right;
    ObjRef operand_left;

    int character;
    ObjRef temp_obj;
    ObjRef duplicate;
    int index;


    inst = INSTRUCTION(ir);
    immediate = SING_EXTEND(IMMEDIATE(ir));
    inst = inst >> INSTRUCTION_SHIFT;

    switch (inst) {
        case (PUSHC):
            bigFromInt(immediate);
            push_reference(bip.res);
            break;
        case (ADD):
            bip.op2 = pop_reference();
            bip.op1 = pop_reference();
            if(bip.op1 == NULL || bip.op2  == NULL){
                fatalError("Error: access on nil");
            }

            bigAdd();
            push_reference(bip.res);
            break;
        case (SUB):
            bip.op2 = pop_reference();
            bip.op1 = pop_reference();

            if(bip.op1 == NULL || bip.op2 == NULL){
                fatalError("Error: access on nil");
            }

            bigSub();
            push_reference(bip.res);
            break;
        case (MUL):
            bip.op2 = pop_reference();
            bip.op1 = pop_reference();

            if(bip.op1 == NULL || bip.op2 == NULL){
                fatalError("Error: access on nil");
            }

            bigMul();
            push_reference(bip.res);
            break;
        case (DIV):
            bip.op2 = pop_reference();
            bip.op1 = pop_reference();

            if(bip.op1 == NULL || bip.op2 == NULL){
                fatalError("Error: access on nil");
            }

            bigDiv();
            push_reference(bip.res);
            break;
        case (MOD):
            bip.op2 = pop_reference();
            bip.op1 = pop_reference();

            if(bip.op1 == NULL || bip.op2 == NULL){
                fatalError("Error: access on nil");
            }

            bigDiv();
            push_reference(bip.rem);
            break;
        case (RDINT):
            bigRead(stdin);
            push_reference(bip.res);
            break;
        case (WRINT):
            bip.op1 = pop_reference();
            if(bip.op1 == NULL){
                fatalError("Error: access on nil");
            }
            bigPrint(stdout);
            break;
        case (RDCHR):
            character = getchar();
            bigFromInt(character);
            push_reference(bip.res);
            break;
        case (WRCHR):
            bip.op1 = pop_reference();
            if(bip.op1 == NULL){
                fatalError("Error: access on nil");
            }
            printf("%c", bigToInt());
            break;
        case (PUSHG):
            pushg(immediate);
            break;
        case (POPG):
            popg(immediate);
            break;
        case (ASF):
            asf(immediate);
            break;
        case (RSF):
            rsf();
            break;
        case (PUSHL):
            pushl(immediate);
            break;
        case (POPL):
            popl(immediate);
            break;
        case (EQ):
            bip.op2 = pop_reference();
            bip.op1 = pop_reference();

            if(bip.op1 == NULL || bip.op2 == NULL){
                fatalError("Error: access on nil");
            }

            if (bigCmp() == 0) {
                bigFromInt(1);
            } else {
                bigFromInt(0);
            }
            push_reference(bip.res);
            break;
        case (NE):
            bip.op2 = pop_reference();
            bip.op1 = pop_reference();
            if(bip.op1 == NULL || bip.op2 == NULL){
                fatalError("Error: access on nil");
            }
            if (bigCmp() != 0) {
                bigFromInt(1);
            } else {
                bigFromInt(0);
            }
            push_reference(bip.res);
            break;
        case (LT):
            bip.op2 = pop_reference();
            bip.op1 = pop_reference();

            if(bip.op1 == NULL || bip.op2 == NULL){
                fatalError("Error: access on nil");
            }

            if (bigCmp() < 0) {
                bigFromInt(1);
            } else {
                bigFromInt(0);
            }
            push_reference(bip.res);
            break;
        case (LE):
            bip.op2 = pop_reference();
            bip.op1 = pop_reference();

            if(bip.op1 == NULL || bip.op2 == NULL){
                fatalError("Error: access on nil");
            }

            if (bigCmp() <= 0) {
                bigFromInt(1);
            } else {
                bigFromInt(0);
            }
            push_reference(bip.res);
            break;
        case (GT):
            bip.op2 = pop_reference();
            bip.op1 = pop_reference();

            if(bip.op1 == NULL || bip.op2 == NULL){
                fatalError("Error: access on nil");
            }

            if (bigCmp() > 0) {
                bigFromInt(1);
            } else {
                bigFromInt(0);
            }
            push_reference(bip.res);
            break;
        case (GE):
            bip.op2 = pop_reference();
            bip.op1 = pop_reference();
            if(bip.op1 == NULL || bip.op2 == NULL){
                fatalError("Error: access on nil");
            }

            if (bigCmp() >= 0) {
                bigFromInt(1);
            } else {
                bigFromInt(0);
            }
            push_reference(bip.res);
            break;
        case (JMP):
            if (immediate < 0) {
                exit(99);
            }
            pc = immediate;
            break;
        case (BRF):
            bigFromInt(0);
            bip.op1 = bip.res;
            bip.op2 = pop_reference();

            if(bip.op2 == NULL){
                fatalError("Error: access on nil");
            }

            if (bigCmp() == 0) {
                if (immediate < 0) {
                    exit(99);
                }
                pc = immediate;
            }
            break;
        case (BRT):
            bigFromInt(1);
            bip.op1 = bip.res;
            bip.op2 = pop_reference();

            if(bip.op2 == NULL){
                fatalError("Error: access on nil");
            }

            if (bigCmp() == 0) {
                if (immediate < 0) {
                    exit(99);
                }
                pc = immediate;
            }
            break;
        case (CALL):
            push_number(pc);
            pc = immediate;
            break;
        case (RET):
            if (immediate < 0) {
                exit(99);
            }
            pc = pop_number();
            break;
        case (DROP):
            for(index = 0; index<immediate; index++){
                stack.slots[stack.sp] = emptySlot;
                stack.sp--;
            }
            break;
        case (PUSHR):
            push_reference(returnRegister);
            break;
        case (POPR):
            returnRegister = pop_reference();
            break;
        case (DUP):
            temp_obj = pop_reference();
            duplicate = temp_obj;
            push_reference(temp_obj);
            push_reference(duplicate);
            break;
        case (NEW):
            temp_obj = newComObject(immediate);
            for (index = 0;index<GET_SIZE(temp_obj); index++){
                GET_REFS(temp_obj)[index] = NULL;
            }
            push_reference(temp_obj);
            break;
        case (GETF):
            temp_obj = pop_reference();
            if(temp_obj == NULL){
                fatalError("Error: access on nil");
            }
            else if(immediate>GET_SIZE(temp_obj)){
                fatalError("Error: array out of bounds");
            }
            push_reference(GET_REFS(temp_obj)[immediate]);
            break;
        case (PUTF):
            operand_right = pop_reference();
            temp_obj = pop_reference();
            if(temp_obj == NULL){
                fatalError("Error: access on nil");
            }
            GET_REFS(temp_obj)[immediate] = operand_right;
            break;
        case (NEWA):
            bip.op1 = pop_reference();

            if(bip.op1==NULL){
                fatalError("Error: access on nil");
            }
            temp_obj = newComObject(bigToInt());
            for (index = 0;index<GET_SIZE(temp_obj); index++){
                GET_REFS(temp_obj)[index] = NULL;
            }
            push_reference(temp_obj);
            break;
        case (GETFA):
            bip.op2 = pop_reference();
            temp_obj = pop_reference();
            bip.op1 = bip.op2;
            if(temp_obj == NULL || bip.op1==NULL){
                fatalError("Error: access on nil");
            }
            else if(bigToInt()>GET_SIZE(temp_obj)){
                fatalError("Error: Array out of bounds");
            }
            bip.op1 = bip.op2;
            push_reference(GET_REFS(temp_obj)[bigToInt()]);
            break;
        case (PUTFA):
            operand_right = pop_reference(); /*value*/
            bip.op1 = pop_reference(); /*index*/
            temp_obj = pop_reference(); /*array*/
            if(temp_obj == NULL ||bip.op1 == NULL){
                fatalError("Error: access on nil");
            }
            GET_REFS(temp_obj)[bigToInt()] = operand_right;
            break;
        case (GETSZ):
            temp_obj = pop_reference();
            if(temp_obj == NULL){
                fatalError("Error: access on nil");
            }
            bigFromInt(GET_SIZE(temp_obj));
            push_reference(bip.res);
            break;
        case (PUSHN):
            temp_obj = NULL;
            push_reference(temp_obj);
            break;
        case (REFEQ):
            operand_right = pop_reference();
            operand_left = pop_reference();
            if(operand_right == operand_left){
                bigFromInt(1);
            }
            else{
                bigFromInt(0);
            }
            push_reference(bip.res);
            break;
        case (REFNE):
            operand_right = pop_reference();
            operand_left = pop_reference();
            if(operand_right == operand_left){
                bigFromInt(0);
            }
            else{
                bigFromInt(1);
            }
            push_reference(bip.res);
            break;
        default:
            fatalError("Error: unknown Instruction");
            break;
    }
}

void debugMode(void) {
    unsigned int ir;
    int runflag = 0;
    breakPoint = -1;
    pc = 0;
    while (HALT != (ir = *(instruction + pc))) {
        pc = pc + 1;
        printInst(ir);
        runflag = askDebugChoice(ir);
        if (runflag == 1) {
            return;
        } else if (runflag == 2) {
            continue;
        } else if (runflag == 0) {
            exec(ir);
        } else {
            fatalError("Should never Happen");
        }
    }
}

int runDebug(void) {
    unsigned int ir;
    exec(*(instruction + pc - 1));
    while (HALT != (ir = *(instruction + pc))) {
        if (breakPoint == pc) {
            return 2;
        }
        pc = pc + 1;
        exec(ir);
    }
    return 1;
}

int askDebugChoice(unsigned int ir) {
    char input[40];
    int match = 0;
    ObjRef obj;
    int counter;
    ObjRef obj2;

    do {
        printf("DEBUG: inspect, list, breakpoint, step, run, quit?\n");
        if (fgets(input, sizeof(input), stdin)) {
            if ((compareStrings("inspect\n", input))) {
                printf("DEBUG [inspect]: stack, data, object?\n");
                fgets(input, sizeof(input), stdin);
                if (compareStrings("stack", input)) {
                    printStack();
                    printInst(ir);
                } else if (compareStrings("data", input)) {
                    printData();
                    printInst(ir);
                } else if (compareStrings("object", input)) {
                    scanf("%p",(void**)&obj);
                    if(IS_PRIMITIV(obj)){
                        printf("<primitiv object>\n");
                        printf("value: ");
                        bip.op1 = obj;
                        bigPrint(stdout);
                        printf("\n");
                        printf("size in hex: %x\n", obj->size);
                    }
                    else{
                        printf("<compound object>\n");
                        for (counter  = 0; counter < GET_SIZE(obj); ++counter) {
                            obj2 = GET_REFS(obj)[counter];
                            if(obj2 == NULL){
                                printf("field[%.4d]: (objref) (nil)\n",counter);
                            }
                            else{
                                printf("field[%.4d]: (objref) %p\n",counter, (void*)GET_REFS(obj)[counter]);
                            }
                        }
                    }
                }
                match = 1;
            } else if (compareStrings("list\n", input)) {
                printCode();
                match = 1;
            } else if (compareStrings("breakpoint\n", input)) {
                printf("DEBUG [breakpoint]: ");
                if (breakPoint == -1) {
                    printf("cleared\n");
                } else {
                    printf("set at %d\n", breakPoint);
                }
                printf("DEBUG [breakpoint]: address to set, -1 to clear, <ret> for no change?\n");
                fgets(input, sizeof(input), stdin);
                setBreakpoint(input);
                match = 1;
            } else if (compareStrings("step\n", input)) {
                break;
            } else if (compareStrings("run\n", input)) {
                return runDebug();
            } else if (compareStrings("quit\n", input)) {
                exit(0);
            } else {
                match = 1;
            }
        }
    } while (match);
    return 0;
}

int compareStrings(char *a, char *b) {
    size_t stringlength = strlen(b);
    int size = (int) stringlength;
    int counter = 0;
    char currentChar1 = a[counter];
    char currentChar2 = b[counter];
    char previewChar;
    if (stringlength == 1)return 0;
    while (counter < size) {
        if (currentChar1 != currentChar2) {
            if (counter + 1 < size) {
                previewChar = a[counter + 1];
                if (counter + 2 < size) return 0;
                if (currentChar2 != previewChar) {
                    return 0;
                }
            } else {
                return 0;
            }
        }
        counter++;
    }
    return 1;
}

void printStack(void) {
    int counter = stack.sp;
    int counter_2 = 0;
    while (counter != -1) {
        if (counter == stack.sp && counter == stack.fp) {
            printf("sp, fp\t--->\t %04d:\t++++\n", stack.sp - counter_2);
        } else if (counter == stack.sp) {
            printf("sp\t--->\t %04d:\t++++\n", stack.sp - counter_2);
        } else if (counter == stack.fp) {
            if (stack.slots[counter].isObjRef) {
                printf("fp\t--->\t %04d:\t%s%p\n", stack.sp - counter_2, "(objref) ",
                       (void *) stack.slots[counter].u.objRef);
            } else {
                printf("fp\t--->\t %04d:\t%s%d\n", stack.sp - counter_2, "(number) ",
                       stack.slots[counter].u.number);
            }
        } else {
            if (stack.slots[counter].isObjRef) {
                printf("\t\t %04d:\t%s%p\n", stack.sp - counter_2, "(objref) ",
                       (void *)stack.slots[counter].u.objRef);

            } else {
                printf("\t\t %04d:\t%s%d\n", stack.sp - counter_2, "(number) ", stack.slots[counter].u.number);

            }
        }
        counter_2++;
        counter--;
    }
    printf("\t\t\t--- bottom of stack ---\n");
}

void printData(void) {
    int statCounter = 0;
    if (static_var_count == 0) {
        printf("\t\t --- end of data ---\n");
        return;
    }
    while (statCounter < static_var_count) {
        printf("data[%04d]:\t %p\n", statCounter, (void*)GET_REFS(staticData_comp)[statCounter]);
        statCounter++;
    }
    printf("\t\t --- end of data ---\n");

}


void printCode(void) {
    int inst;
    int immediate;
    int counter = 0;
    while (counter < instr_count) {
        inst = INSTRUCTION(*(instruction + counter));
        immediate = SING_EXTEND(IMMEDIATE(*(instruction + counter)));
        inst = inst >> INSTRUCTION_SHIFT;
        printf("%04d:\t", counter);
        switch (inst) {
            case (HALT):
                printf("halt\n");
                break;
            case (PUSHC):
                printf("push:\t%d\n", immediate);
                break;
            case (ADD):
                printf("add\n");
                break;
            case (SUB):
                printf("sub\n");
                break;
            case (MUL):
                printf("mul\n");
                break;
            case (DIV):
                printf("div\n");
                break;
            case (MOD):
                printf("mod\n");
                break;
            case (RDINT):
                printf("rdint\n");
                break;
            case (WRINT):
                printf("wrint\n");
                break;
            case (RDCHR):
                printf("rdchr\n");
                break;
            case (WRCHR):
                printf("wrchhr\n");
                break;
            case (PUSHG):
                printf("pushg:\t%d\n", immediate);
                break;
            case (POPG):
                printf("popg:\t%d\n", immediate);
                break;
            case (ASF):
                printf("asf:\t%d\n", immediate);
                break;
            case (RSF):
                printf("rsf:\t%d\n", immediate);
                break;
            case (PUSHL):
                printf("pushl:\t%d\n", immediate);
                break;
            case (POPL):
                printf("popl:\t%d\n", immediate);
                break;
            case (EQ):
                printf("eq\n");
                break;
            case (NE):
                printf("ne\n");
                break;
            case (LT):
                printf("lt\n");
                break;
            case (LE):
                printf("le\n");
                break;
            case (GT):
                printf("gt\n");
                break;
            case (GE):
                printf("ge\n");
                break;
            case (JMP):
                break;
            case (BRF):
                printf("brf:\t%d\n", immediate);
                break;
            case (BRT):
                printf("brt:\t%d\n", immediate);
                break;
            case (CALL):
                printf("CALL:\t%d\n", immediate);
                break;
            case (RET):
                printf("RET:\n");
                break;
            case (DROP):
                printf("DROP:\t%d\n", immediate);
                break;
            case (PUSHR):
                printf("PUSHR:\t");
                break;
            case (POPR):
                printf("POPR:\t");
                break;
            case (DUP):
                printf("DUP:\t");
                break;
            case(NEW):
                printf("new: \t%d\n", immediate);
                break;
            case(GETF):
                printf("getf: \t%d\n", immediate);
                break;
            case(PUTF):
                printf("putf: \t%d\n", immediate);
                break;
            case (NEWA):
                printf("newa\n");
                break;
            case (GETFA):
                printf("getfa\n");
                break;
            case (PUTFA):
                printf("putfa\n");
                break;
            case (GETSZ):
                printf("getsz\n");
                break;
            case (PUSHN):
                printf("pushn\n");
                break;
            case (REFEQ):
                printf("refeq\n");
                break;
            case (REFNE):
                printf("refne\n");
                break;
            default:
                fatalError("Error: unknown Instruction");
                break;
        }
        counter++;
    }
    printf("\t--- end of code ---\n");
}

void setBreakpoint(char *input) {
    int pos = 0;
    int length = (int) strlen(input);
    int number = 0;
    int flagMinus = 0;
    if (input[pos] == '\n') {
        return;
    }
    while (pos < length - 1) {
        if (input[pos] == '-') {
            flagMinus = 1;
            pos++;
            continue;
        } else if ((input[pos] - 48) < 0 || (input[pos] - 48) > 9) {
            return;
        }
        number = getNumberFromString(input[pos], number);
        pos++;
    }
    if (flagMinus) {
        /*'-' detected and value is 1 -> -1 -> breakpoint reset*/
        if (number == 1) {
            breakPoint = -1;
            printf("DEBUG [breakpoint]: now cleared\n");
        }
    } else {
        printf("DEBUG [breakpoint]: now set at %d\n", number);
        breakPoint = number;
    }
}

int getNumberFromString(char c, int pre) {
    return 10 * pre + c - 48;
}

void* malloc_heap(int dataSize){
    /* malloc_heap
     *
     * start address + size of heap -> max adress
     * currently first free address -> evaluates by adding the datasize of the needed space of the new object
     * after allocating space-> check if end address + current adress exceeds or equals the max adress -> no more memory
     * */
    char *obj;
    char *end_ptr;

    end_ptr = heap.target+heap.heapSize;
    if(heap.currentFreeTarget+dataSize > end_ptr){
        collect_Garbage();
        end_ptr = heap.target+heap.heapSize;
        if(heap.currentFreeTarget+dataSize > end_ptr){
            fatalError("Error: heap overflow");
        }
    }
    obj = heap.currentFreeTarget;
    heap.currentFreeTarget += dataSize;

    return obj;
}

ObjRef newPrimObject(int dataSize) {
    ObjRef objRef;

    objRef = malloc_heap(sizeof(unsigned int) +
                         dataSize * sizeof(unsigned char));
    if ((void*)objRef == NULL) {
        fatalError("Error: newPrimObject() got no memory");
    }
    objRef->size = (unsigned int)dataSize;
    return objRef;
}

ObjRef newComObject(int objectCount){
    ObjRef o;
    o = malloc_heap(sizeof(unsigned int) + objectCount * sizeof(ObjRef));
    if ((void*)o == NULL) {
        fatalError("Error: newComObject() got no memory");
    }
    o->size = (unsigned int)objectCount | MSB;
    return o;
}



void fatalError(char *msg) {
    printf("%s", msg);
    exit(99);
}    /* print a message and exit */


/*Garbage Collector*/

void collect_Garbage(void){
    gc_Started_Flag = 1;
    if(gc_Stats_Flag){
        initGcStats();
    }
    flip_memory();
    copy_root_objects();

    scan_Root_Objects();
    if(gc_Purge_Flag){
        gcPurge();
    }
    if(gc_Stats_Flag){
        gcStats();
    }
}

void initGcStats(void){
    relocBytes = 0;
    relocCount = 0;
    livingObjectsCount = 0;
    livingObjectsBytes = 0;
    freeSizeInBytes = heap.heapSize;
}

void flip_memory(void){
    void *target = heap.target;
    heap.target = heap.source;
    heap.source = target;
    heap.currentFreeTarget = heap.target;
}


void copy_root_objects(void){
    int i = 0;
    staticData_comp = relocate(staticData_comp);
    returnRegister = relocate(returnRegister);
    for (i = 0; i < stack.stackSize ; ++i) {
        if(i>=stack.sp){
            stack.slots[i] = emptySlot;
        }
        else if(stack.slots[i].u.objRef == NULL && i>=stack.sp){
            break;
        }
        else if(stack.slots[i].isObjRef){
            stack.slots[i].u.objRef = relocate(stack.slots[i].u.objRef);
        }
    }

    bip.op1 = relocate(bip.op1);
    bip.op2 = relocate(bip.op2);
    bip.res = relocate(bip.res);
    bip.rem = relocate(bip.rem);
}

ObjRef relocate(ObjRef orig){
    ObjRef copy;
    if(orig == NULL){
        copy = NULL;
    }
    else if(IS_BROKENHEART(orig)){
        copy = (ObjRef)((heap.target) + (GET_FORWARD_OFFSET(orig)));

    }
    else{
        copy = copyObjToFreeMem(orig);
        relocCount++;
        relocBytes+=GET_SIZE(copy);
        orig->size = (unsigned int)((char*)copy - heap.target) ;
        orig->size = orig->size | (MBHB);
    }
    return copy;
}

void scan_Root_Objects(void){
    int i;
    char *scan = heap.target;
    int offset;

    while (scan != heap.currentFreeTarget){
        if(!IS_PRIMITIV((ObjRef)scan)){
            for (i = 0; i <GET_SIZE((ObjRef)scan); ++i) {
                livingObjectsCount++;
                GET_REFS((ObjRef) scan)[i] = relocate(GET_REFS((ObjRef) scan)[i]);
                if((GET_REFS((ObjRef) scan)[i]) != NULL && !IS_BROKENHEART(GET_REFS((ObjRef) scan)[i])){
                    livingObjectsBytes += GET_SIZE( (GET_REFS((ObjRef) scan)[i]) );
                }
            }
        }
        if(IS_PRIMITIV((ObjRef)scan)) {
            offset = sizeof(unsigned int) + GET_SIZE((ObjRef) scan);
        }
        else{
            offset = sizeof(unsigned int) + GET_SIZE((ObjRef)scan) * sizeof(ObjRef);

        }
        scan += offset;
    }
}

ObjRef copyObjToFreeMem(ObjRef objRef){
    int copySize;
    ObjRef o;
    if(IS_PRIMITIV(objRef)){
        copySize = sizeof(unsigned int)+(GET_SIZE(objRef));
    }
    else{
        copySize = sizeof(unsigned int)+sizeof(ObjRef)*GET_SIZE(objRef);
    }
    memcpy(heap.currentFreeTarget,objRef,copySize);
    o = (ObjRef)heap.currentFreeTarget;
    freeSizeInBytes -= copySize;
    heap.currentFreeTarget += copySize;

    return o;
}

void gcPurge(void){
    memset(heap.source, 0,heap.heapSize);
}

void gcStats(void) {
    printf("Garbage Collector:\n\t"
                   "%d objects (%d bytes) allocated since last collection\n\t"
                   "%d objects (%d bytes) copied during this collection\n\t"
                   "%d of %d bytes free after this collection\n",
           relocCount, relocBytes, livingObjectsCount, livingObjectsBytes, freeSizeInBytes, heap.heapSize);
}
