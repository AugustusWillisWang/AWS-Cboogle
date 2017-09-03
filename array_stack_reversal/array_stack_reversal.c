/*
 * @Author: Augustus.Wang 
 * @Date: 2017-07-18 19:47:17 
 * @Last Modified by: Augustus.Wang
 * @Last Modified time: 2017-07-18 20:09:26
 */
#define stacksize 10000
#include <stdio.h>
//use stack to reverse an array
//use array to get a stack
int top;
int bottom;
int* s [stacksize];
int* A [stacksize]={1,2,3,4,5} //example array


void error(){
	print("error");
}

void s.make(){
	top=0;
	bottom=0;
}

int empty(bottom,top){
	return (top<=bottom);
}

void s.push(int new_element){
	s[top]=new_element;
	top++;
}

int  s,pop(){
	if(!empty(bottom,top));
	else error();
	top--;
	return s[top];
}

int s.top(){
	if (!empty(bottom,top))
	return s[top];
	else error();
}

void stack_reverse (int n)
{
	int i;
	i = 1;
	s.make();
	while ( i <= n )
	{
		s.push(A[i]);
		i = i + 1;
	}
	i = 1;
	while ( i <= n )
	{
		int temp= s.pop();
		A[i] =temp
		//assert ( seq_cat_reverse_equals(s, bottom, top, A, 1, i-1, old(A), 1, n) );		
		i = i + 1;
	}
}

