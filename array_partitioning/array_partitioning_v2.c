/*
 * @Author: Augustus.Wang 
 * @Date: 2017-07-18 19:10:41 
 * @Last Modified by: Augustus.Wang
 * @Last Modified time: 2017-07-18 19:19:44
 */
//array_partitioning_v2

int swap(int* array,int num1,int num2);
int partition (int* array, int left, int right, int pivot);

int swap(int* array,int num1,int num2){
    if (array==0)return -1;
    int temp;
    temp= array[num1];
    array[num1]=array[num2];
	array[num2]=temp;
}

int partition (int* array, int left, int right, int pivot){
    if (left<=right&&array!=0);
    else return -1;
    while(left!=right){
        while(left!=right&&array[left]<pivot){
            while (left!= right&&array){left}<=pivot{
                left++;
            }
            while (left!=right&&pivot<=array[right]){
                right--;
            }
        }
        swap(array,left,right)        
    }
    if(pivot<=B[left])return (left-1);
    else return left;
}