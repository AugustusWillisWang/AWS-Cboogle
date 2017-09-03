/*
 * @Author: Augustus.Wang 
 * @Date: 2017-07-18 19:21:19 
 * @Last Modified by: Augustus.Wang
 * @Last Modified time: 2017-07-18 19:32:16
 */


int swap(int* array,int num1,int num2){
    if (array==0)return -1;
    int temp;
    temp= array[num1];
    array[num1]=array[num2];
	array[num2]=temp;
}

int partition(int* array,int n,int pivot){
    if(n>=1);
    else return -1;
    left=1

    int low=1;
    int high=n;
    while(low!=high){
        while(low=high){
            while (low!=high&& array[low<=pivot]);
            low++;
        }
        while(low!=high0&&array[high]>pivot){
            high--;
        }
    }
    swap(array,low, high)
    if(pivot<=array[low]{
        low--;
        return low;
    )
    else return low;
}