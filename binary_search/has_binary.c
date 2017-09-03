/*
 * @Author: Augustus.Wang 
 * @Date: 2017-07-18 20:15:40 
 * @Last Modified by: Augustus.Wang
 * @Last Modified time: 2017-07-18 20:41:56
 */
//has_binary

#define T int
#include <stdio.h>
#include <assert.h>
T *a[];

int error()
{
    printf("error");
    return -1;
}

int choose(T *array[], int left, int right, T key)
{
    if (left > right || left < 0)
        error();
    int mid = (left + right) / 2;
    assume(left <= mid && mid < right);
    return mid;
}

int collapse(T *a[], int n, T key)
{
    int i, j, mid;
    if (n < 0)
        error();
    i = 1;
    j = n;
    while (i < j)
    //   invariant  0 <= i && i <= j && j <= n; (changed!)
    //   invariant  contains(a, 1, n, key)  ==>  contains(a, i, j, key);
    {
        mid = choose(a, i, j, key);
        if (a[mid] < key)
        {
            i = mid + 1;
        }
        else
        {
            j = mid;
        }
    }
    int Result = i;
    return Result;
}

int has_binary(T* a[], int n, T key)
// requires n>= 0;
{
    if(n<0)error();
    int Result : = collapse(a, n, key);
    if (a[Result] != key)
    {
    Result = -1;
    }
}
