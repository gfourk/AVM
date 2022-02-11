#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>
#include <stdarg.h>
#include <math.h>
#include "avm.h"

FILE* avm = NULL;

enum avm_memcell_t{
	number_m,string_m,bool_m,table_m,userfunc_m,libfunc_m,nil_m,undef_m
};

struct avm_table;
struct avm_memcell{
	enum avm_memcell_t type;
	union {
		double numVal;
		char* strVal;
		unsigned char boolVal;
		struct avm_table* tableVal;
		unsigned funcVal;
		char* libfuncVal;
	}data;
};

#define AVM_STACKSIZE 4096
#define AVM_WIPEOUT(m) memset(&m,0,sizeof(m))

struct avm_memcell stack[AVM_STACKSIZE];

struct avm_table_bucket{
	struct avm_memcell* key;
	struct avm_memcell* value;
	struct avm_table_bucket* next;
};

struct avm_table {
	unsigned refCounter;
	struct avm_table_bucket* strIndexed;
	struct avm_table_bucket* numIndexed;
	unsigned total;
};


static void avm_initstack(){
	unsigned i = 0;
	for(i=0;i<AVM_STACKSIZE;i++){
		AVM_WIPEOUT(stack[i]);
		stack[i].type = undef_m;
	}
}

void avm_tabledecrefcounter(struct avm_table* t);

void avm_memcellclear(struct avm_memcell* m){
	switch(m->type){
		case number_m:
			m->data.numVal = 0;
			break;
		case string_m:
			free(m->data.strVal);m->data.strVal = NULL;
			break;
		case bool_m:
			m->data.boolVal = 0;
			break;
		case table_m:
			avm_tabledecrefcounter(m->data.tableVal);
			break;
		case userfunc_m:
			m->data.funcVal = 0;
			break;
		case libfunc_m:
			m->data.libfuncVal = NULL;
			break;
		default:
			assert(m->type==nil_m || m->type==undef_m);
	}
	m->type = undef_m;
}

void avm_tablebucketsdestroy(struct avm_table_bucket** p){
	struct avm_table_bucket* b = NULL;
	struct avm_table_bucket* del = NULL;
	for(b=(*p); b!=NULL;){
		del = b;
		b = b->next;
		avm_memcellclear(del->key);
		avm_memcellclear(del->value);
		free(del->key);
		free(del->value);
		free(del);
	}
	(*p) = NULL;
}

struct avm_table* avm_tablenew(void){
	struct avm_table* t = (struct avm_table*)malloc(sizeof(struct avm_table));
	t->refCounter = 0;
	t->total = 0;
	t->strIndexed = NULL;
	t->numIndexed = NULL;

	return t;
}

void avm_tabledestroy(struct avm_table* t){
	avm_tablebucketsdestroy(&t->strIndexed);
	avm_tablebucketsdestroy(&t->numIndexed);
	free(t);
}

void avm_tableincrefcounter(struct avm_table* t){
	t->refCounter++;
}

void avm_tabledecrefcounter(struct avm_table* t){
	assert(t->refCounter>0);
	t->refCounter--;
	if(!t->refCounter)avm_tabledestroy(t);
}

#define AVM_STACKENV_SIZE 4

struct avm_memcell ax,bx,cx;
struct avm_memcell retval;
unsigned top,topsp;

double consts_getnumber(unsigned index){
	return numConsts[index];
}

char* consts_getstring(unsigned index){
	return stringConsts[index];
}

char* libfuncs_getused(unsigned index){
	return namedLibFuncs[index];
}

struct avm_memcell* avm_translate_operand(struct vmarg* arg,struct avm_memcell* reg){
	switch(arg->type){
		case global_a:{
			fprintf(avm,"translate global\n");
			return &stack[AVM_STACKSIZE-1-arg->val];
		}
		case local_a: {
			fprintf(avm,"translate local\n");
			return &stack[topsp-arg->val];
		}
		case formal_a: {
			fprintf(avm,"translate formal\n");
			return &stack[topsp+AVM_STACKENV_SIZE+1+arg->val];
		}
		case retval_a: {
			fprintf(avm,"translate retval\n");
			return &retval;
		}
		case number_a: {
			fprintf(avm,"translate number\n");
			reg->type = number_m;
			reg->data.numVal = consts_getnumber(arg->val);
			return reg;
		}
		case string_a: {
			fprintf(avm,"translate string\n");
			reg->type = string_m;
			reg->data.strVal = consts_getstring(arg->val);
			return reg;
		}
		case bool_a: {
			fprintf(avm,"translate bool\n");
			reg->type = bool_m;
			reg->data.boolVal = arg->val;
			return reg;
		}
		case nil_a: {
			fprintf(avm,"translate nil\n");
			reg->type = nil_m;
			return reg;
		}
		case userfunc_a: {
			fprintf(avm,"translate userfunc\n");
			reg->type = userfunc_m;
			reg->data.funcVal = arg->val;
			return reg;
		}
		case libfunc_a: {
			fprintf(avm,"translate libfunc\n");
			reg->type = libfunc_m;
			reg->data.libfuncVal = libfuncs_getused(arg->val);
			return reg;
		}
		default:
			assert(0);
	}
}

unsigned char executionFinished = 0;
unsigned pc = 1;
unsigned currLine = 0;
unsigned codesize = 0;
struct instruction* code = NULL;

extern void avm_assign(struct avm_memcell* lv,struct avm_memcell* rv);

void execute_assign(struct instruction* instr){
	struct avm_memcell *lv = NULL,*rv = NULL;
	lv = avm_translate_operand(&instr->result,(struct avm_memcell*)0);
	rv = avm_translate_operand(&instr->arg1,&ax);
	assert( (lv!=NULL) && ((&stack[AVM_STACKSIZE]>lv && &stack[top]<lv) || lv==&retval) );
	assert((rv!=NULL));
	avm_assign(lv,rv);
}

void avm_assign(struct avm_memcell* lv,struct avm_memcell* rv){
	if(lv==rv)return;
	if(lv->type==table_m && rv->type==table_m && rv->data.tableVal==lv->data.tableVal)
		return;
	if(rv->type==undef_m)fprintf(stderr,"AVM Warning\nassigning from 'undef' content!");
	avm_memcellclear(lv);
	memcpy(lv,rv,sizeof(struct avm_memcell));
	if(lv->type == number_m)fprintf(avm,"assign lv = %f\n",lv->data.numVal);
	if(rv->type == number_m)fprintf(avm,"assign rv %f\n",rv->data.numVal);
	if(lv->type==string_m)lv->data.strVal = strdup(rv->data.strVal);
	else if(lv->type==table_m)avm_tableincrefcounter(lv->data.tableVal);
}


unsigned totalActuals = 0;

void avm_dec_top(){
	if(!top){
		fprintf(stderr,"AVM Error\nstack overflow");
		executionFinished = 1;
	}
	else --top;
}

void avm_push_envvalue(unsigned val){
	stack[top].type = number_m;
	stack[top].data.numVal = val;
	avm_dec_top();
}

void avm_callsaveenvironment(void){
	avm_push_envvalue(totalActuals);
	avm_push_envvalue(pc+1);
	avm_push_envvalue(top+totalActuals+2);
	avm_push_envvalue(topsp);
}

struct userFunc* avm_getfuncinfo(unsigned adress){
	unsigned j = 0;
	for(j=0;j<totalUserFuncs;j++){
		if(userFuncs[j]->adress == adress)return userFuncs[j];
	}
	assert(0);
}

void execute_funcenter(struct instruction* instr){
	struct userFunc* funcinfo = NULL;
	struct avm_memcell* func = avm_translate_operand(&instr->result,&ax);
	assert(func!=NULL);
	fprintf(avm,"funcenter pc = %u function = %u adress = %u\n",pc,func->data.funcVal,
		userFuncs[func->data.funcVal]->adress);
	assert(pc==userFuncs[func->data.funcVal]->adress);
	funcinfo = avm_getfuncinfo(pc);
	topsp = top;
	top = top - funcinfo->localsize;
}

unsigned avm_get_envvalue(unsigned i){
	unsigned val = 0;
	assert(stack[i].type == number_m);
	val = (unsigned)stack[i].data.numVal;
	assert( stack[i].data.numVal == (double)val );
	return val;
}

#define AVM_NUMACTUALS_OFFSET 4
#define AVM_SAVEDPC_OFFSET 3
#define AVM_SAVEDTOP_OFFSET 2
#define AVM_SAVEDTOPSP_OFFSET 1

void execute_funcexit(struct instruction* unused){
	unsigned oldTop = top;
	/*totalActuals = avm_get_envvalue(topsp+AVM_NUMACTUALS_OFFSET);*/
	top = avm_get_envvalue(topsp+AVM_SAVEDTOP_OFFSET);
	pc = avm_get_envvalue(topsp+AVM_SAVEDPC_OFFSET);
	topsp = avm_get_envvalue(topsp+AVM_SAVEDTOPSP_OFFSET);

	while(++oldTop<=top)avm_memcellclear(&stack[oldTop]);
}

extern char* avm_tostring(struct avm_memcell*);
extern void avm_calllibfunc(char* libfuncname);
extern void avm_callsaveenvironment(void);
void execute_cycle(void);

void execute_call(struct instruction* instr){
	char* s = NULL;
	struct avm_memcell* func = avm_translate_operand(&instr->result,&ax);
	assert(func);
	avm_callsaveenvironment();
	totalActuals = 0;
	switch(func->type){
		case userfunc_m :{
			pc = userFuncs[func->data.funcVal]->adress;
			assert(pc<currInstruction);
			assert(instructions[pc].opcode==funcenter_v);
			break;
		}
		case string_m: avm_calllibfunc(func->data.strVal);break;/*execute libfunc*/
		case libfunc_m: avm_calllibfunc(func->data.libfuncVal);break;
		default:{
			s = avm_tostring(func);
			fprintf(stderr,"AVM Error\ncall: cannot bind %s to function!",s);
			free(s);
			executionFinished = 1;
		}
	}
}

typedef void (*library_func_t)(void);

library_func_t avm_getlibraryfunc(char* id);

void avm_calllibfunc(char* id){
	library_func_t f = avm_getlibraryfunc(id);
	if(!f){
		fprintf(stderr,"AVM Error\nunsupported lib func %s called!",id);
		executionFinished = 1;
	}
	else{
		topsp = top;
		(*f)();
		if(!executionFinished)execute_funcexit((struct instruction*)0);
	}
}

unsigned avm_totalactuals(void){
	return avm_get_envvalue(topsp+AVM_NUMACTUALS_OFFSET);
}

struct avm_memcell* avm_getactual(unsigned i){
	assert(i<avm_totalactuals());
	return &stack[topsp+AVM_STACKENV_SIZE+i+1];
}

void avm_registerlibfunc(char* id,library_func_t addr);

void execute_pusharg(struct instruction* instr){
	struct avm_memcell* arg = avm_translate_operand(&instr->result,&ax);
	assert(arg);
	avm_assign(&stack[top],arg);
	if(arg->type == number_m)fprintf(avm,"push %f\n",arg->data.numVal);
	totalActuals++;
	avm_dec_top();
}

typedef char* (*tostring_func_t)(struct avm_memcell*);

char* number_tostring(struct avm_memcell* m){
	char s[30];
	sprintf(s,"%f%c",m->data.numVal,'\0');
	return strdup(s);
}
char* string_tostring(struct avm_memcell* m){return strdup(m->data.strVal);}
char* bool_tostring(struct avm_memcell* m){
	char* s[]={"true","false"};
	return strdup(s[m->data.boolVal]);
}
char* table_tostring(struct avm_memcell* m){
	char* s = NULL;
	struct avm_table_bucket* b = NULL;
	printf("\n");
	for(b=m->data.tableVal->strIndexed; b!=NULL;b = b->next){
		s = avm_tostring(b->key);
		if(b->key->type!=table_m){
			printf("%s : ",s);
			free(s);
		}
		s = avm_tostring(b->value);
		if(b->value->type!=table_m){
			printf("%s\n",s);
			free(s);
		}
	}
	for(b=m->data.tableVal->numIndexed; b!=NULL;b = b->next){
		s = avm_tostring(b->key);
		if(b->key->type!=table_m){
			printf("%s : ",s);
			free(s);
		}
		s = avm_tostring(b->value);
		if(b->value->type!=table_m){
			printf("%s\n",s);
			free(s);
		}
	}
	printf("\n");
	return NULL;
}
char* userfunc_tostring(struct avm_memcell* m){
	return strdup(userFuncs[m->data.funcVal]->id);
}
char* libfunc_tostring(struct avm_memcell* m){return strdup(m->data.libfuncVal);}
char* nil_tostring(struct avm_memcell* m){return strdup("nil");}
char* undef_tostring(struct avm_memcell* m){assert(0);return NULL;}

tostring_func_t tostringFuncs[] = {
	number_tostring,
	string_tostring,
	bool_tostring,
	table_tostring,
	userfunc_tostring,
	libfunc_tostring,
	nil_tostring,
	undef_tostring
};

char* avm_tostring(struct avm_memcell* m){
	assert(m->type>=0 && m->type<=undef_m);
	return (*tostringFuncs[m->type])(m);
}

typedef double (*arithmetic_func_t)(double x,double y);

double add_impl(double x,double y){return x+y;}
double sub_impl(double x,double y){return x-y;}
double mul_impl(double x,double y){return x*y;}
double div_impl(double x,double y){return x/y;}
double mod_impl(double x,double y){
	return ((unsigned)x%(unsigned)y);
}

arithmetic_func_t arithmeticFuncs[] = {
	add_impl,
	sub_impl,
	mul_impl,
	div_impl,
	mod_impl
};

#define execute_add execute_arithmetic
#define execute_sub execute_arithmetic
#define execute_mul execute_arithmetic
#define execute_div execute_arithmetic
#define execute_mod execute_arithmetic

void execute_arithmetic(struct instruction* instr){
	arithmetic_func_t op;
	struct avm_memcell *lv = NULL,*rv1 = NULL,*rv2 = NULL;
	lv = avm_translate_operand(&instr->result,(struct avm_memcell*)0);
	rv1 = avm_translate_operand(&instr->arg1,&ax);
	rv2 = avm_translate_operand(&instr->arg2,&bx);
	assert(lv&&((&stack[AVM_STACKSIZE]>lv && &stack[top]<lv) || lv==&retval));
	assert(rv1 && rv2);
	if(rv1->type!=number_m || rv2->type!=number_m){
		fprintf(stderr,"AVM Error\nnot a number in arithmetic");
		executionFinished = 1;
	}
	else{
		op = arithmeticFuncs[instr->opcode-add_v];
		if(lv!=rv1 && lv!=rv2)avm_memcellclear(lv);
		lv->type = number_m;
		lv->data.numVal = (*op)(rv1->data.numVal,rv2->data.numVal);
	}
}

typedef unsigned char (*tobool_func_t)(struct avm_memcell*);

unsigned char number_tobool(struct avm_memcell* m){return m->data.numVal!=0;}
unsigned char string_tobool(struct avm_memcell* m){return m->data.strVal[0]!='\0';}
unsigned char bool_tobool(struct avm_memcell* m){return m->data.boolVal;}
unsigned char table_tobool(struct avm_memcell* m){return 1;}
unsigned char userfunc_tobool(struct avm_memcell* m){return 1;}
unsigned char libfunc_tobool(struct avm_memcell* m){return 1;}
unsigned char nil_tobool(struct avm_memcell* m){return 0;}
unsigned char undef_tobool(struct avm_memcell* m){assert(0);return 0;}

tobool_func_t toboolFuncs [] = {
	number_tobool,
	string_tobool,
	bool_tobool,
	table_tobool,
	userfunc_tobool,
	libfunc_tobool,
	nil_tobool,
	undef_tobool
};

unsigned char avm_tobool(struct avm_memcell* m){
	assert(m->type>=0 && m->type<=undef_m);
	return (*toboolFuncs[m->type])(m);
}

char* typeStrings[] = {
	"number","string","bool","table","userfunc","libfunc","nil","undef"
};


void execute_newtable(struct instruction* instr){
	struct avm_memcell* lv = avm_translate_operand(&instr->result,(struct avm_memcell*)0);
	assert((lv!=NULL)&&((&stack[AVM_STACKSIZE]>lv && &stack[top]<lv) || lv==&retval));
	avm_memcellclear(lv);
	lv->type = table_m;
	lv->data.tableVal = avm_tablenew();
	avm_tableincrefcounter(lv->data.tableVal);
}

struct avm_memcell* avm_tablegetelem(struct avm_table* table,struct avm_memcell* index){
	struct avm_table_bucket* head = NULL;
	switch(index->type){
		case number_m:{
			head = table->numIndexed;
			fprintf(avm,"getelem head = %p\n",(void*)head);
			while(head!=NULL){
				fprintf(avm,"getelem head->numVal = %f\n",head->key->data.numVal);
				fprintf(avm,"getelem index->numVal = %f\n",index->data.numVal);
				if(head->key->data.numVal == index->data.numVal)return head->value;
				head = head->next;
			}
			break;
		}
		case string_m:
			head = table->strIndexed;
			fprintf(avm,"getelem head = %p\n",(void*)head);
			while(head!=NULL){
				fprintf(avm,"getelem head->strVal = %s\n",head->key->data.strVal);
				fprintf(avm,"getelem index->strVal = %s\n",index->data.strVal);
				if(strcmp(head->key->data.strVal,index->data.strVal)==0)return head->value;
				head = head->next;
			}
			break;
		default:
			assert(0);
	}
	assert(0);
	return NULL;
}

void avm_tablesetelem(struct avm_table** table,
	struct avm_memcell* index,struct avm_memcell* content)
{
	struct avm_table_bucket* head = NULL;
	struct avm_table_bucket* previous = NULL;
	switch(index->type){
		case number_m:{
			head = (*table)->numIndexed;
			fprintf(avm,"setelem head = %p\n",(void*)head);
			while(head!=NULL){
				fprintf(avm,"setelem head->numVal = %f\n",head->key->data.numVal);
				fprintf(avm,"setelem index->numVal = %f\n",index->data.numVal);
				if(head->key->data.numVal == index->data.numVal){
					avm_assign(head->value,content);
					return;
				}
				previous = head;
				head = head->next;
			}
			head = (struct avm_table_bucket*)malloc(sizeof(struct avm_table_bucket));
			if(head == NULL){
				fprintf(stderr,"Out of memory\n");
				exit(1);
			}
			head->key = (struct avm_memcell*)malloc(sizeof(struct avm_memcell));
			if(head->key == NULL){
				fprintf(stderr,"Out of memory\n");
				exit(1);
			}
			head->value = (struct avm_memcell*)malloc(sizeof(struct avm_memcell));
			if(head->value == NULL){
				fprintf(stderr,"Out of memory\n");
				exit(1);
			}
			head->key->type = head->value->type = undef_m;
			avm_assign(head->key,index);
			avm_assign(head->value,content);
			head->next = NULL;
			if(previous!=NULL)previous->next = head;
			else (*table)->numIndexed = head;
			return;
		}
		case string_m:
			head = (*table)->strIndexed;
			fprintf(avm,"setelem head = %p\n",(void*)head);
			while(head!=NULL){
				fprintf(avm,"setelem head->strVal = %s\n",head->key->data.strVal);
				fprintf(avm,"setelem index->strVal = %s\n",index->data.strVal);
				if(strcmp(head->key->data.strVal,index->data.strVal)==0){
					avm_assign(head->value,content);
					return;
				}
				previous = head;
				head = head->next;
			}
			head = (struct avm_table_bucket*)malloc(sizeof(struct avm_table_bucket));
			if(head == NULL){
				fprintf(stderr,"Out of memory\n");
				exit(1);
			}
			head->key = (struct avm_memcell*)malloc(sizeof(struct avm_memcell));
			if(head->key == NULL){
				fprintf(stderr,"Out of memory\n");
				exit(1);
			}
			head->value = (struct avm_memcell*)malloc(sizeof(struct avm_memcell));
			if(head->value == NULL){
				fprintf(stderr,"Out of memory\n");
				exit(1);
			}
			head->key->type = head->value->type = undef_m;
			avm_assign(head->key,index);
			avm_assign(head->value,content);
			head->next = NULL;
			if(previous!=NULL)previous->next = head;
			else (*table)->strIndexed = head;
			return;
		default:
			assert(0);
	}
	assert(0);
}

void execute_tablegetelem(struct instruction* instr){
	char *is = NULL,*ts = NULL;
	struct avm_memcell *content = NULL,*lv = NULL,*t = NULL,*i = NULL;
	lv = avm_translate_operand(&instr->result,(struct avm_memcell*)0);
	t = avm_translate_operand(&instr->arg1,(struct avm_memcell*)0);
	i = avm_translate_operand(&instr->arg2,&ax);
	assert((lv!=NULL)&&((&stack[AVM_STACKSIZE]>lv && &stack[top]<lv) || lv==&retval));

	assert((t!=NULL) && (&stack[AVM_STACKSIZE]>t) && (&stack[top]<t));
	avm_memcellclear(lv);
	lv->type = nil_m;
	if(t->type!=table_m)
		fprintf(stderr,"AVM Error\nillegal use of type %s as table",typeStrings[t->type]);
	else{
		content = avm_tablegetelem(t->data.tableVal,i);
		if(content){
			if(content->type==number_m)fprintf(avm,"content = %f\n",content->data.numVal);
			avm_assign(lv,content);
		}
		else{
			ts = avm_tostring(t);
			is = avm_tostring(i);
			fprintf(stderr,"AVM Warning\n%s[%s] not found!",ts,is);
			free(ts);
			free(is);
		}
	}
}

void execute_tablesetelem(struct instruction* instr){
	struct avm_memcell *t = NULL,*i = NULL,*c = NULL;
	c = avm_translate_operand(&instr->result,&ax);
	t = avm_translate_operand(&instr->arg1,(struct avm_memcell*)0);
	i = avm_translate_operand(&instr->arg2,&bx);
	assert(i!=NULL && c!=NULL);
	assert((t!=NULL) && (&stack[AVM_STACKSIZE]>t) && (&stack[top]<t));
	if(t->type!=table_m)
		fprintf(stderr,"AVM Error\nillegal use of type %s as table",typeStrings[t->type]);
	else{
		avm_tablesetelem(&t->data.tableVal,i,c);
	}
}

void execute_jump(struct instruction* instr){
	assert(instr->result.type == label_a);
	pc = instr->result.val;
}

void execute_jeq(struct instruction* instr){
	unsigned char result = 0;
	struct avm_memcell* rv1 = NULL;
	struct avm_memcell* rv2 = NULL;
	assert(instr->result.type == label_a);
	rv1 = avm_translate_operand(&instr->arg1,&ax);
	rv2 = avm_translate_operand(&instr->arg2,&bx);
	if(rv1->type == undef_m || rv2->type==undef_m){
		fprintf(stderr,"AVM Error\n'undef' involved in equality");
		executionFinished = 1;
	}
	else if(rv1->type == nil_m || rv2->type==nil_m){
		result=(rv1->type == nil_m && rv2->type==nil_m);
	}
	else if(rv1->type == bool_m || rv2->type==bool_m){
		result=(avm_tobool(rv1) == avm_tobool(rv2));
	}
	else if(rv1->type != rv2->type){
		fprintf(stderr,"AVM Error\n%s == %s is illegal!",
			typeStrings[rv1->type],typeStrings[rv2->type]);
		executionFinished = 1;
	}
	else{
		switch(rv1->type){
			case number_m:{
				result = (rv1->data.numVal == rv2->data.numVal);
				break;
			}
			case string_m:{
				result = (strcmp(rv1->data.strVal,rv2->data.strVal)==0);
				break;
			}
			case table_m:{
				result = (rv1->data.tableVal == rv2->data.tableVal);
				break;
			}
			case userfunc_m:{
				result = (userFuncs[rv1->data.funcVal]->adress ==
						userFuncs[rv2->data.funcVal]->adress);
				break;
			}
			case libfunc_m:{
				result = (strcmp(rv1->data.libfuncVal,rv2->data.libfuncVal)==0);
				break;
			}
			default:assert(0);
		}
	}
	if(!executionFinished && result)
		pc = instr->result.val;
}

void execute_jne(struct instruction* instr){
	unsigned char result = 0;
	struct avm_memcell* rv1 = NULL;
	struct avm_memcell* rv2 = NULL;
	assert(instr->result.type == label_a);
	rv1 = avm_translate_operand(&instr->arg1,&ax);
	rv2 = avm_translate_operand(&instr->arg2,&bx);
	if(rv1->type == undef_m || rv2->type==undef_m){
		fprintf(stderr,"AVM Error\n'undef' involved in !=");
		executionFinished = 1;
	}
	else if(rv1->type == nil_m || rv2->type==nil_m){
		result=!(rv1->type == nil_m && rv2->type==nil_m);
	}
	else if(rv1->type == bool_m || rv2->type==bool_m){
		result=(avm_tobool(rv1) != avm_tobool(rv2));
	}
	else if(rv1->type != rv2->type){
		fprintf(stderr,"AVM Error\n%s != %s is illegal!",
			typeStrings[rv1->type],typeStrings[rv2->type]);
		executionFinished = 1;
	}
	else{
		switch(rv1->type){
			case number_m:{
				result = (rv1->data.numVal != rv2->data.numVal);
				break;
			}
			case string_m:{
				result = (strcmp(rv1->data.strVal,rv2->data.strVal)!=0);
				break;
			}
			case table_m:{
				result = (rv1->data.tableVal != rv2->data.tableVal);
				break;
			}
			case userfunc_m:{
				result = (userFuncs[rv1->data.funcVal]->adress !=
						userFuncs[rv2->data.funcVal]->adress);
				break;
			}
			case libfunc_m:{
				result = (strcmp(rv1->data.libfuncVal,rv2->data.libfuncVal)!=0);
				break;
			}
			default:assert(0);
		}
	}
	if(!executionFinished && result)
		pc = instr->result.val;
}


void execute_jle(struct instruction* instr){
	unsigned char result = 0;
	struct avm_memcell* rv1 = NULL;
	struct avm_memcell* rv2 = NULL;
	assert(instr->result.type == label_a);
	rv1 = avm_translate_operand(&instr->arg1,&ax);
	rv2 = avm_translate_operand(&instr->arg2,&bx);
	if(rv1->type == undef_m || rv2->type==undef_m){
		fprintf(stderr,"AVM Error\n'undef' involved in <=");
		executionFinished = 1;
	}
	else if(rv1->type != rv2->type){
		fprintf(stderr,"AVM Error\n%s <= %s is illegal!",
			typeStrings[rv1->type],typeStrings[rv2->type]);
		executionFinished = 1;
	}
	else{
		switch(rv1->type){
			case number_m:{
				result = (rv1->data.numVal <= rv2->data.numVal);
				break;
			}
			default:{
				fprintf(stderr,"AVM Error\n%s <= %s is illegal!",
					typeStrings[rv1->type],typeStrings[rv2->type]);
				executionFinished = 1;
			}
		}
	}
	if(!executionFinished && result)
		pc = instr->result.val;
}


void execute_jge(struct instruction* instr){
	unsigned char result = 0;
	struct avm_memcell* rv1 = NULL;
	struct avm_memcell* rv2 = NULL;
	assert(instr->result.type == label_a);
	rv1 = avm_translate_operand(&instr->arg1,&ax);
	rv2 = avm_translate_operand(&instr->arg2,&bx);
	if(rv1->type == undef_m || rv2->type==undef_m){
		fprintf(stderr,"AVM Error\n'undef' involved in >=");
		executionFinished = 1;
	}
	else if(rv1->type != rv2->type){
		fprintf(stderr,"AVM Error\n%s >= %s is illegal!",
			typeStrings[rv1->type],typeStrings[rv2->type]);
		executionFinished = 1;
	}
	else{
		switch(rv1->type){
			case number_m:{
				result = (rv1->data.numVal >= rv2->data.numVal);
				break;
			}
			default:{
				fprintf(stderr,"AVM Error\n%s >= %s is illegal!",
					typeStrings[rv1->type],typeStrings[rv2->type]);
				executionFinished = 1;
			}
		}
	}
	if(!executionFinished && result)
		pc = instr->result.val;
}


void execute_jlt(struct instruction* instr){
	unsigned char result = 0;
	struct avm_memcell* rv1 = NULL;
	struct avm_memcell* rv2 = NULL;
	assert(instr->result.type == label_a);
	rv1 = avm_translate_operand(&instr->arg1,&ax);
	rv2 = avm_translate_operand(&instr->arg2,&bx);
	if(rv1->type == undef_m || rv2->type==undef_m){
		fprintf(stderr,"AVM Error\n'undef' involved in <");
		executionFinished = 1;
	}
	else if(rv1->type != rv2->type){
		fprintf(stderr,"AVM Error\n%s < %s is illegal!",
			typeStrings[rv1->type],typeStrings[rv2->type]);
		executionFinished = 1;
	}
	else{
		switch(rv1->type){
			case number_m:{
				result = (rv1->data.numVal < rv2->data.numVal);
				break;
			}
			default:{
				fprintf(stderr,"AVM Error\n%s < %s is illegal!",
					typeStrings[rv1->type],typeStrings[rv2->type]);
				executionFinished = 1;
			}
		}
	}
	if(!executionFinished && result)
		pc = instr->result.val;
}


void execute_jgt(struct instruction* instr){
	unsigned char result = 0;
	struct avm_memcell* rv1 = NULL;
	struct avm_memcell* rv2 = NULL;
	assert(instr->result.type == label_a);
	rv1 = avm_translate_operand(&instr->arg1,&ax);
	rv2 = avm_translate_operand(&instr->arg2,&bx);
	if(rv1->type == undef_m || rv2->type==undef_m){
		fprintf(stderr,"AVM Error\n'undef' involved in >");
		executionFinished = 1;
	}
	else if(rv1->type != rv2->type){
		fprintf(stderr,"AVM Error\n%s > %s is illegal!",
			typeStrings[rv1->type],typeStrings[rv2->type]);
		executionFinished = 1;
	}
	else{
		switch(rv1->type){
			case number_m:{
				result = (rv1->data.numVal > rv2->data.numVal);
				break;
			}
			default:{
				fprintf(stderr,"AVM Error\n%s > %s is illegal!",
					typeStrings[rv1->type],typeStrings[rv2->type]);
				executionFinished = 1;
			}
		}
	}
	if(!executionFinished && result)
		pc = instr->result.val;
}

typedef void (*execute_func_t)(struct instruction*);

#define AVM_MAX_INSTRUCTIONS (unsigned)tablesetelem_v

execute_func_t executeFuncs[] = {
	execute_assign,
	execute_add,
	execute_sub,
	execute_mul,
	execute_div,
	execute_mod,
	execute_jump,
	execute_jeq,
	execute_jne,
	execute_jle,
	execute_jge,
	execute_jlt,
	execute_jgt,
	execute_call,
	execute_pusharg,
	execute_funcenter,
	execute_funcexit,
	execute_newtable,
	execute_tablegetelem,
	execute_tablesetelem,
};

void execute_cycle(void){
	static char* o[] = {"assign","add","sub","mul","div","mod","jump",
	"jeq","jne","jle","jge","jlt","jgt","call","push","funcenter","funcexit",
	"newtable","tablegetelem","tablesetelem","nop"};
	unsigned oldPC = 0;
	struct instruction* instr = NULL;
	if(executionFinished)return;
	else
		if(pc==currInstruction){
			executionFinished = 1;
			return;
		}
		else{
			assert(pc<currInstruction && pc>0);
			instr = &instructions[pc];
			fprintf(avm,"pc = %u\n",pc);
			fprintf(avm,"top = %u topsp = %u actuals = %u\n",top,topsp,totalActuals);
			assert(instr->opcode>=assign_v && instr->opcode<=tablesetelem_v);
			fprintf(avm,"order = %s\n",o[instr->opcode]);
			if(instr->srcLine)
				currLine = instr->srcLine;
			oldPC = pc;
			(*executeFuncs[instr->opcode])(instr);
			if(pc==oldPC)
				pc++;
		}
}

void libfunc_print(void){
	char* s = NULL;
	unsigned j = 0;
	unsigned n = avm_totalactuals();
	for(j=0; j<n;j++){
		s = avm_tostring(avm_getactual(j));
		if(s!=NULL){
			printf("%s",s);
			free(s);
		}
	}
}

void libfunc_input(void){
	double d;
	char s[80] = {0,};
	scanf("%s",s);
	d = atof(s);
	avm_memcellclear(&retval);
	if( d || s[0]=='0'){
		retval.type = number_m;
		retval.data.numVal = d;
	}
	else if(strncmp(s,"true",4)==0){
		retval.type = bool_m;
		retval.data.boolVal = 1;
	}
	else if(strncmp(s,"false",5)==0){
		retval.type = bool_m;
		retval.data.boolVal = 0;
	}
	else if(strncmp(s,"nil",3)==0){
		retval.type = nil_m;
	}
	else{
		retval.type = string_m;
		retval.data.strVal = strdup(s);
	}
}

void libfunc_objectmemberkeys(void){
	unsigned j = 0;
	struct avm_table_bucket* head = NULL;
	struct avm_table_bucket* b = NULL;
	struct avm_table* newtab = NULL;
	struct avm_memcell* tab = NULL;
	unsigned n = avm_totalactuals();
	if(n!=1){
		fprintf(stderr,"AVM Error\none argument (not %d) expected in 'objectcopy'!",n);
		exit(1);
	}
	tab = avm_getactual(0);
	if(tab->type!=table_m){
		fprintf(stderr,"AVM Error\ntable argument expected in 'objectcopy'!");
		exit(1);
	}
	newtab = avm_tablenew();
	for(b=tab->data.tableVal->strIndexed; b!=NULL;b = b->next){
		head = (struct avm_table_bucket*)malloc(sizeof(struct avm_table_bucket));
		if(head == NULL){
			fprintf(stderr,"Out of memory\n");
			exit(1);
		}
		head->key = (struct avm_memcell*)malloc(sizeof(struct avm_memcell));
		if(head->key == NULL){
			fprintf(stderr,"Out of memory\n");
			exit(1);
		}
		head->value = (struct avm_memcell*)malloc(sizeof(struct avm_memcell));
		if(head->value == NULL){
			fprintf(stderr,"Out of memory\n");
			exit(1);
		}
		head->key->type = number_m;
		head->key->data.numVal = j;
		head->value->type = undef_m;
		avm_assign(head->value,b->key);
		head->next = newtab->numIndexed;
		newtab->numIndexed = head;
		j++;
	}
	for(b=tab->data.tableVal->numIndexed; b!=NULL;b = b->next){
		head = (struct avm_table_bucket*)malloc(sizeof(struct avm_table_bucket));
		if(head == NULL){
			fprintf(stderr,"Out of memory\n");
			exit(1);
		}
		head->key = (struct avm_memcell*)malloc(sizeof(struct avm_memcell));
		if(head->key == NULL){
			fprintf(stderr,"Out of memory\n");
			exit(1);
		}
		head->value = (struct avm_memcell*)malloc(sizeof(struct avm_memcell));
		if(head->value == NULL){
			fprintf(stderr,"Out of memory\n");
			exit(1);
		}
		head->key->type = number_m;
		head->key->data.numVal = j;
		head->value->type = undef_m;
		avm_assign(head->value,b->key);
		head->next = newtab->numIndexed;
		newtab->numIndexed = head;
		j++;
	}
	avm_memcellclear(&retval);
	retval.type = table_m;
	retval.data.tableVal = newtab;
	avm_tableincrefcounter(retval.data.tableVal);
	newtab = NULL;
}

void libfunc_objecttotalmembers(void){
	unsigned j = 0;
	struct avm_table_bucket* b = NULL;
	struct avm_memcell* tab = NULL;
	unsigned n = avm_totalactuals();
	if(n!=1){
		fprintf(stderr,"AVM Error\none argument (not %d) expected in 'objectcopy'!",n);
		exit(1);
	}
	tab = avm_getactual(0);
	if(tab->type!=table_m){
		fprintf(stderr,"AVM Error\ntable argument expected in 'objectcopy'!");
		exit(1);
	}
	for(b=tab->data.tableVal->strIndexed; b!=NULL;b = b->next){
		j++;
	}
	for(b=tab->data.tableVal->numIndexed; b!=NULL;b = b->next){
		j++;
	}
	avm_memcellclear(&retval);
	retval.type = number_m;
	retval.data.numVal = j;
}

void libfunc_objectcopy(void){
	struct avm_memcell* tab = NULL;
	unsigned n = avm_totalactuals();
	if(n!=1){
		fprintf(stderr,"AVM Error\none argument (not %d) expected in 'objectcopy'!",n);
		exit(1);
	}
	tab = avm_getactual(0);
	if(tab->type!=table_m){
		fprintf(stderr,"AVM Error\ntable argument expected in 'objectcopy'!");
		exit(1);
	}
	avm_memcellclear(&retval);
	avm_assign(&retval,tab);
}

void libfunc_totalarguments(void){
	unsigned p_topsp = avm_get_envvalue(topsp+AVM_SAVEDTOPSP_OFFSET);
	avm_memcellclear(&retval);
	if(!p_topsp){
		fprintf(stderr,"AVM Error\n'totalarguments' called outside a function!");
		retval.type = nil_m;
	}
	else{
		retval.type = number_m;
		retval.data.numVal = avm_get_envvalue(p_topsp+AVM_NUMACTUALS_OFFSET);
	}
}

void libfunc_argument(void){
	unsigned n = 0;
	unsigned p_topsp = avm_get_envvalue(topsp+AVM_SAVEDTOPSP_OFFSET);
	avm_memcellclear(&retval);
	n = avm_totalactuals();
	if(!p_topsp){
		fprintf(stderr,"AVM Error\n'argument' called outside a function!");
		retval.type = nil_m;
	}
	if(n!=1)
		fprintf(stderr,"AVM Error\none argument (not %d) expected in 'argument'!",n);
	else{
		avm_memcellclear(&retval);
		if(
			(avm_getactual(0)->type == number_m)&&
			((int)avm_getactual(0)->data.numVal%1==0 && avm_getactual(0)->data.numVal>=0)&&
		(avm_get_envvalue(topsp+AVM_NUMACTUALS_OFFSET) > avm_getactual(0)->data.numVal)&&
			(p_topsp+AVM_NUMACTUALS_OFFSET+1+avm_getactual(0)->data.numVal < 4096)&&
			(p_topsp+AVM_NUMACTUALS_OFFSET+1+avm_getactual(0)->data.numVal > top)
		){
			retval = stack[p_topsp+AVM_STACKENV_SIZE+(int)avm_getactual(0)->data.numVal];
		}
		else{
			retval.type = nil_m;
		}
	}
}

void libfunc_typeof(void){
	unsigned n = avm_totalactuals();
	if(n!=1)
		fprintf(stderr,"AVM Error\none argument (not %d) expected in 'typeof'!",n);
	else{
		avm_memcellclear(&retval);
		retval.type = string_m;
		retval.data.strVal = strdup(typeStrings[avm_getactual(0)->type]);
	}
}

void libfunc_strtonum(void){
	unsigned n = avm_totalactuals();
	if(n!=1)
		fprintf(stderr,"AVM Error\none argument (not %d) expected in 'strtonum'!",n);
	else{
		assert(avm_getactual(0)->type==string_m);
		avm_memcellclear(&retval);
		retval.type = number_m;
		retval.data.numVal = atof(avm_getactual(0)->data.strVal);
	}
}

void libfunc_sqrt(void){
	unsigned n = avm_totalactuals();
	if(n!=1)
		fprintf(stderr,"AVM Error\none argument (not %d) expected in 'sqrt'!",n);
	else{
		assert(avm_getactual(0)->type==number_m);
		avm_memcellclear(&retval);
		retval.type = number_m;
		retval.data.numVal = sqrt(avm_getactual(0)->data.numVal);
	}
}

void libfunc_cos(void){
	unsigned n = avm_totalactuals();
	if(n!=1)
		fprintf(stderr,"AVM Error\none argument (not %d) expected in 'cos'!",n);
	else{
		assert(avm_getactual(0)->type==number_m);
		avm_memcellclear(&retval);
		retval.type = number_m;
		retval.data.numVal = cos(avm_getactual(0)->data.numVal);
	}
}

void libfunc_sin(void){
	unsigned n = avm_totalactuals();
	if(n!=1)
		fprintf(stderr,"AVM Error\none argument (not %d) expected in 'sin'!",n);
	else{
		assert(avm_getactual(0)->type==number_m);
		avm_memcellclear(&retval);
		retval.type = number_m;
		retval.data.numVal = sin(avm_getactual(0)->data.numVal);
	}
}

library_func_t avm_getlibraryfunc(char* id){
	if(strcmp("print",id)==0)return libfunc_print;
	else if(strcmp("input",id)==0)return libfunc_input;
	else if(strcmp("objectmemberkeys",id)==0)return libfunc_objectmemberkeys;
	else if(strcmp("objecttotalmembers",id)==0)return libfunc_objecttotalmembers;
	else if(strcmp("objectcopy",id)==0)return libfunc_objectcopy;
	else if(strcmp("totalarguments",id)==0)return libfunc_totalarguments;
	else if(strcmp("argument",id)==0)return libfunc_argument;
	else if(strcmp("typeof",id)==0)return libfunc_typeof;
	else if(strcmp("strtonum",id)==0)return libfunc_strtonum;
	else if(strcmp("sqrt",id)==0)return libfunc_sqrt;
	else if(strcmp("cos",id)==0)return libfunc_cos;
	else if(strcmp("sin",id)==0)return libfunc_sin;
	fprintf(stderr,"AVM Error\nNot such a libfunction!");
	assert(0);
}

int main(void){
	avm = fopen("avm.txt","w");
	binary_readinstructions();
	avm_initstack();
	top = 4095 - programVarOffset;
	topsp = top;
	pc = 1;
	while(!executionFinished){
		fprintf(avm,"cycle = %u\n",k++);
		execute_cycle();
	}
	fprintf(avm,"ending pc = %u\n",pc);
	fprintf(avm,"top = %u topsp = %u actuals = %u\n",top,topsp,totalActuals);
	while(top<4096){
		avm_memcellclear(&stack[top]);
		top++;
	}
	avm_memcellclear(&retval);
	topsp = top;
	fprintf(avm,"after stack clear top = %u topsp = %u actuals = %u\n",
		top,topsp,totalActuals);
	freeall();
	fclose(avm);
	return 0;
}

