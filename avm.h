extern FILE* avm;
extern char* strdup(char* s);

enum vmopcode{
	assign_v,add_v,sub_v,mul_v,div_v,mod_v,jump_v,jeq_v,jne_v,jle_v,
	jge_v,jlt_v,jgt_v,call_v,push_v,funcenter_v,funcexit_v,
	newtable_v,tablegetelem_v,tablesetelem_v
};

enum vmarg_t{
	label_a,global_a,formal_a,local_a,number_a,string_a,bool_a,nil_a,
	userfunc_a,libfunc_a,retval_a,undef_a
};

struct vmarg{
	enum vmarg_t type;
	unsigned val;
};

struct instruction{
	enum vmopcode opcode;
	struct vmarg result;
	struct vmarg arg1;
	struct vmarg arg2;
	unsigned srcLine;
};

struct userFunc{
	unsigned adress;
	unsigned localsize;
	char* id;
};

unsigned k = 1;
unsigned programVarOffset = 0;
unsigned currInstruction = 1;
struct instruction* instructions = NULL;

double* numConsts = NULL;
unsigned totalNumConsts = 0;
char** stringConsts = NULL;
unsigned totalstringConsts = 0;
char** namedLibFuncs;
unsigned totalNameLibFuncs = 0;
struct userFunc** userFuncs = NULL;
unsigned totalUserFuncs = 0;

void binary_readinstruction(FILE* fp,unsigned j)
{
	unsigned label;
	unsigned char c;
	fread(&c,sizeof(unsigned char),1,fp);
	instructions[j].opcode = (enum vmopcode)c;
	fread(&c,sizeof(unsigned char),1,fp);
	instructions[j].result.type = (enum vmarg_t)c;
	fread(&label,sizeof(unsigned int),1,fp);
	instructions[j].result.val = label;
	fread(&c,sizeof(unsigned char),1,fp);
	instructions[j].arg1.type = (enum vmarg_t)c;
	fread(&label,sizeof(unsigned int),1,fp);
	instructions[j].arg1.val = label;
	fread(&c,sizeof(unsigned char),1,fp);
	instructions[j].arg2.type = (enum vmarg_t)c;
	fread(&label,sizeof(unsigned int),1,fp);
	instructions[j].arg2.val = label;
	fread(&label,sizeof(unsigned int),1,fp);
	instructions[j].srcLine = label;
}

void from_binary_magicnumber(FILE* fp)
{
	unsigned int magicnum;
	fread(&magicnum,sizeof(unsigned int),1,fp);
	if(magicnum != (unsigned int)340200501){
		fprintf(stderr,"AVM Error wrong magic num!");
		exit(1);
	}
}

void from_binary_strings(FILE* fp)
{
	char c = 0;
	unsigned i = 0;
	unsigned j = 0;
	unsigned size = 0;
	unsigned total;
	fread(&total,sizeof(unsigned int),1,fp);
	totalstringConsts = total;
	fread(&c,sizeof(char),1,fp);
	assert(c=='\n');
	stringConsts = (char**)malloc(sizeof(char*)*(totalstringConsts));
	if(stringConsts == NULL){
		fprintf(stderr,"Out of memory\n");
		exit(1);
	}
	for(i=0;i<total;i++){
		fread(&j,sizeof(unsigned int),1,fp);
		size = j-1;
		fread(&c,sizeof(char),1,fp);
		assert(c=='\t');
		stringConsts[i] = (char*)malloc(sizeof(char)*(size+1));
		if(stringConsts[i] == NULL){
			fprintf(stderr,"Out of memory\n");
			exit(1);
		}
		for(j=0;j<size;j++){
			fread(&stringConsts[i][j],sizeof(char),1,fp);
		}
		fread(&stringConsts[i][j],sizeof(char),1,fp);
		fread(&c,sizeof(char),1,fp);
		assert(c=='\n');
	}
}

void from_binary_numbers(FILE* fp)
{
	char c;
	double d;
	unsigned i = 0;
	unsigned total;
	fread(&total,sizeof(unsigned int),1,fp);
	totalNumConsts = total;
	fread(&c,sizeof(char),1,fp);
	assert(c=='\n');
	numConsts = (double*)malloc(sizeof(double)*(totalNumConsts));
	if(numConsts == NULL){
		fprintf(stderr,"Out of memory\n");
		exit(1);
	}
	for(i=0;i<total;i++){
		fread(&d,sizeof(double),1,fp);
		numConsts[i] = d;
		fread(&c,sizeof(char),1,fp);
		assert(c=='\n');
	}
}

void from_binary_userfunc(FILE* fp,unsigned i)
{
	char c;
	unsigned j;
	unsigned size;
	userFuncs[i] = (struct userFunc*)malloc(sizeof(struct userFunc));
	if(userFuncs[i] == NULL){
		fprintf(stderr,"Out of memory\n");
		exit(1);
	}
	fread(&j,sizeof(unsigned int),1,fp);
	userFuncs[i]->adress = j;
	fread(&c,sizeof(char),1,fp);
	assert(c=='\t');
	fread(&j,sizeof(unsigned int),1,fp);
	userFuncs[i]->localsize = j;
	fread(&c,sizeof(char),1,fp);
	assert(c=='\t');
	fread(&j,sizeof(unsigned int),1,fp);
	size = j-1;
	fread(&c,sizeof(char),1,fp);
	assert(c=='\t');
	userFuncs[i]->id = (char*)malloc(sizeof(char)*(size+1));
	if(userFuncs[i]->id == NULL){
		fprintf(stderr,"Out of memory\n");
		exit(1);
	}
	for(j=0;j<size;j++){
		fread(&c,sizeof(char),1,fp);
		userFuncs[i]->id[j] = c;
	}
	fread(&c,sizeof(char),1,fp);
	userFuncs[i]->id[j] = c;
	fread(&c,sizeof(char),1,fp);
	assert(c=='\n');
}

void from_binary_userfunctions(FILE* fp)
{
	char c;
	unsigned i = 0;
	unsigned total;
	fread(&total,sizeof(unsigned int),1,fp);
	totalUserFuncs = total;
	fread(&c,sizeof(char),1,fp);
	assert(c=='\n');
	userFuncs = (struct userFunc**)malloc(sizeof(struct userFunc*)*(totalUserFuncs));
	if(userFuncs == NULL){
		fprintf(stderr,"Out of memory\n");
		exit(1);
	}
	for(i=0;i<total;i++){
		from_binary_userfunc(fp,i);
	}
}

void from_binary_libfunctions(FILE* fp)
{
	char c;
	unsigned j = 0;
	unsigned i = 0;
	unsigned size = 0;
	unsigned total;
	fread(&total,sizeof(unsigned int),1,fp);
	totalNameLibFuncs = total;
	fread(&c,sizeof(char),1,fp);
	assert(c=='\n');
	namedLibFuncs = (char**)malloc(sizeof(char*)*(totalNameLibFuncs));
	if(namedLibFuncs == NULL){
		fprintf(stderr,"Out of memory\n");
		exit(1);
	}
	for(i=0;i<total;i++){
		fread(&j,sizeof(unsigned int),1,fp);
		size = j-1;
		fread(&c,sizeof(char),1,fp);
		assert(c=='\t');
		namedLibFuncs[i] = (char*)malloc(sizeof(char)*(size+1));
		if(namedLibFuncs[i] == NULL){
			fprintf(stderr,"Out of memory\n");
			exit(1);
		}
		for(j=0;j<size;j++){
			fread(&namedLibFuncs[i][j],sizeof(char),1,fp);
		}
		fread(&namedLibFuncs[i][j],sizeof(char),1,fp);
		fread(&c,sizeof(char),1,fp);
		assert(c=='\n');
	}
}

void from_binary_arrays(FILE* fp)
{
	from_binary_strings(fp);
	from_binary_numbers(fp);
	from_binary_userfunctions(fp);
	from_binary_libfunctions(fp);
}

void from_binary_avmfile(FILE* fp){
	from_binary_magicnumber(fp);
	from_binary_arrays(fp);
}

void binary_readinstructions(){
	unsigned j = 0;
	FILE* fp = fopen("instructions.abc","rb");
	if(fp==NULL)fprintf(stderr,"Avm: Error opening file\n");
	from_binary_avmfile(fp);
	fread(&programVarOffset,sizeof(unsigned),1,fp);
	fread(&currInstruction,sizeof(unsigned),1,fp);
	instructions = (struct instruction*)malloc(sizeof(struct instruction)*currInstruction);
	if(instructions == NULL){
		fprintf(stderr,"Out of memory\n");
		exit(1);
	}
	for(j=1;j<currInstruction;j++)binary_readinstruction(fp,j);
	fclose(fp);
}

void freeall(){
	unsigned j = 0;
	for(j=0;j<totalUserFuncs;j++){
		free(userFuncs[j]->id);
		userFuncs[j]->id = NULL;
		free(userFuncs[j]);
		userFuncs[j] = NULL;
	}
	free(userFuncs);
	userFuncs = NULL;
	for(j=0;j<totalNameLibFuncs;j++){
		free(namedLibFuncs[j]);
		namedLibFuncs[j] = NULL;
	}
	for(j=0;j<totalstringConsts;j++){
		free(stringConsts[j]);
		stringConsts[j] = NULL;
	}
	for(j=0;j<totalNameLibFuncs;j++){
		free(namedLibFuncs[j]);
		namedLibFuncs[j] = NULL;
	}
	free(namedLibFuncs);
	namedLibFuncs = NULL;
	free(stringConsts);
	stringConsts = NULL;
	free(numConsts);
	numConsts = NULL;
	free(instructions);
	instructions = NULL;
}

