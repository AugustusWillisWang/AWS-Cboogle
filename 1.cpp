#include<iostream>
#include<fstream>
using namespace std;

namespace classic{
class Box{
    int num;
    public:
    virtual int fun(){
        cout<<"poi";
        return 0;
    }
};

class sbox:public Box{
    public:
    int fun(){
        cout<<"hh";
        return 0;
    }
};
}

using namespace classic;
char temp[100];
int main(){
    class Box box;
    box.fun();
    class sbox hh;
    hh.fun();
    

    int *** array3;
    array3=new int** [8];
    for(int i=0;i<8;i++){
        array3[i]=new int* [9];
        for(int j=0;j<9;j++){
            array3[i][j]=new int [10];
        }
    }

    cout<<array3[2][3][4];

    for(int i=0;i<8;i++){
        for(int j=0;j<9;j++){
            delete [] array3[i][j];
        }
    }
    for(int i=0;i<8;i++){
        delete [] array3[i];
    }
    delete [] array3;
}