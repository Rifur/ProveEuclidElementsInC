#include <stdio.h>
#include <assert.h>
#include <string.h>
#include <stdlib.h>
#include <stdarg.h>

int depth = 0;

#define IN_LEMMA()	depth += 1;
#define OUT_LEMMA() depth -= 1;

void ShowStep(const char *msg, ...) {
	for(int i=0; i<depth; ++i) {
		printf("\t");
	}
	va_list vaptr;
	va_start(vaptr, msg);
	vfprintf(stdout, msg, vaptr);
	va_end(vaptr);
}

typedef struct
{
	char name[64];
} 點;

int 點相等(點 A, 點 B) {
	if(strcmp(A.name, B.name) == 0) {
		//printf("%s %s %s\n", __func__, A.name, B.name);
		return 1;
	}
	return 0;
}

typedef struct
{
	點 端點1;
	點 端點2;
	unsigned int 長度;
	char name[64];
} 線段;

線段 兩點可作一線段(點 A, 點 B) {
	線段 L;
	int c = strcmp(A.name, B.name);
	if(c == 0) {
		assert(0);
	}
	L.端點1 = c < 0 ? A : B;
	L.端點2 = c < 0 ? B : A;
	L.長度 = abs(rand());
	sprintf(L.name, "線段%s,%s", A.name, B.name);
	ShowStep("公設1. %s %s\n", __func__, L.name);
	return L;
}

int 長度相同(線段 A, 線段 B) {
	if(A.長度 == B.長度) {
		ShowStep("公理1: %s |%s|==|%s|\n", __func__, A.name, B.name);
		return 1;
	}
	else
		assert(0);
}

int 相同線段(線段 A, 線段 B) {
	if ((點相等(A.端點1, B.端點1) && 點相等(A.端點2, B.端點2)) 
	 || (點相等(A.端點1, B.端點2) && 點相等(A.端點2, B.端點1))) {
		ShowStep("公理1：%s %s==%s\n", __func__, A.name, B.name);
		return 1;
	} else {
		assert(0);
	}
}

#define LIST_T(T)	\
typedef struct {	\
	T *elements;	\
	int capacity;	\
	int sp;	\
} list_##T;

#define LIST(T)	\
	list_##T


#define LIST_INITIAL(obj, T)	\
	LIST(T) list = { .capacity=10, .sp=0 };	\
	list.elements = calloc(list.capacity, sizeof(T));	\
	obj = list;

#define LIST_APPEND(obj, x)	\
	if(obj.sp == obj.capacity) {	\
		obj.capacity *= 2;	\
		obj.elements = (typeof(x) *)realloc(obj.elements, obj.capacity * sizeof(typeof(x)));	\
	}	\
	obj.elements[obj.sp++] = x;	\

#define LIST_SEARCH(T, cond) \
int list_search_##T(LIST(T) obj, T x) {	\
	for(int i=0; i<obj.sp; ++i) {	\
		if(cond(obj.elements[i], x)) {	\
			return 1;	\
		}	\
	}	\
	return 0;	\
}


LIST_T(點);
LIST_SEARCH(點, 點相等);


typedef struct
{
	點 圓心;
	線段 半徑;
	char name[64];

	LIST(點) 圓上的點;

} 圓;


圓 點和距離可以建造圓(點 圓心, 線段 半徑) {
	圓 O = { .圓心 = 圓心, .半徑=半徑 };
	sprintf(O.name, "圓%s", 圓心.name);
	LIST_INITIAL(O.圓上的點, 點);
	ShowStep("公設3：%s %s 圓心%s 半徑：%s 長度：%d\n", __func__, O.name, 圓心.name, 半徑.name, 半徑.長度);
	return O;
}

typedef struct 等邊三角形
{
	線段 線段1;
	線段 線段2;
	線段 線段3;
} 等邊三角形;

等邊三角形 三邊相等為等邊三角形(線段 L1, 線段 L2, 線段 L3)
{
	ShowStep("引用定義20：%s\n", __func__);
	IN_LEMMA();

	if(!(長度相同(L1, L2) && 長度相同(L2, L3) && 長度相同(L3, L1)))
		assert(0);

	if((點相等(L1.端點1, L2.端點1) || 點相等(L1.端點1, L2.端點2) || 點相等(L1.端點2, L2.端點1) || 點相等(L1.端點2, L2.端點2))
	&& (點相等(L2.端點1, L3.端點1) || 點相等(L2.端點1, L3.端點2) || 點相等(L2.端點2, L3.端點1) || 點相等(L2.端點2, L3.端點2)) 
	&& (點相等(L3.端點1, L1.端點1) || 點相等(L3.端點1, L1.端點2) || 點相等(L3.端點2, L1.端點1) || 點相等(L3.端點2, L1.端點2))) {
		等邊三角形 T = { .線段1=L1, .線段2=L2, .線段3=L3, };
		ShowStep("引用定義20完畢。\n");
		OUT_LEMMA();
		return T;
	}
	else
		assert(0);
}

點 兩圓交集(圓 *O1, 圓 *O2)
{
	ShowStep("引用額外公設6：%s %s交集%s\n", __func__, O1->name, O2->name);
	IN_LEMMA();

	點 C;
	sprintf(C.name, "(C%s%s)", O1->圓心.name, O2->圓心.name);
	if(相同線段(O1->半徑, O2->半徑) && !點相等(O1->圓心, O2->圓心)) {
		
		LIST_APPEND(O1->圓上的點, C);
		LIST_APPEND(O2->圓上的點, C);
		ShowStep("作 %s 上一點 %s\n", O1->name, C.name);

		ShowStep("引用額外公設6完畢。\n");
		OUT_LEMMA();
		return C;
	}
	else {
		assert(0);
	}
}

線段 圓上的點到圓心作線段(圓 O, 點 C) {
	ShowStep("引用定義15：%s %s 點%s\n", __func__, O.name, C.name);
	IN_LEMMA();

	if(!list_search_點(O.圓上的點, C))
		assert(0);

	線段 L = 兩點可作一線段(O.圓心, C);
	L.長度 = O.半徑.長度;

	ShowStep("引用定義15完畢。\n");
	OUT_LEMMA();
	return L;
}

等邊三角形 命題1(線段 線段AB)
{
	ShowStep("%s 證明開始：\n", __func__);	
	IN_LEMMA();

	點 A = 線段AB.端點1;
	點 B = 線段AB.端點2;
	圓 O1 = 點和距離可以建造圓(A, 線段AB);
	圓 O2 = 點和距離可以建造圓(B, 線段AB);
	點 C = 兩圓交集(&O1, &O2);
	線段 AC = 圓上的點到圓心作線段(O1, C);
	線段 BC = 圓上的點到圓心作線段(O2, C);
	等邊三角形 T = 三邊相等為等邊三角形(線段AB, AC, BC);

	ShowStep("%s 證明完畢。\n", __func__);
	OUT_LEMMA();
	
	return T;
}

int main(void) 
{
	點 A = { .name = "A" };
	點 B = { .name = "B" };
	線段 AB = 兩點可作一線段(A, B);

	等邊三角形 T = 命題1(AB);
	return 0;
}
