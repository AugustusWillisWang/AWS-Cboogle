/*
 * @Author: Augustus.Wang 
 * @Date: 2017-07-17 23:31:46 
 * @Last Modified by: Augustus.Wang
 * @Last Modified time: 2017-07-17 23:35:51
 */
int swap(int* array,int num1,int num2);
int partition(int* array,int left, int right,int pivot);

int swap(int* array,int num1,int num2){
    if (array==0)return -1;
    int temp;
    temp= array[num1];
    array[num1]=array[num2];
	array[num2]=temp;
}

int partition(int* array,int left, int right,int pivot){
    if (array==0||left<0||(right-left)<0)return -1;
    int index=left;
    int loopv=left;
    while(loopv<=right){
        if(array[index]<=pivot){
            swap(array,index,loopv);
            index++;
        }
        loopv++;
    }
    return 0;
}

// int main(){
//     return 0;
// }