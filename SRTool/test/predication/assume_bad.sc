
void main(int a)
{

    a = 2;
    if ( a == 2){
        a = 3;
    }         else{
        a = 4 ;
    }
    assume (a==3);
    assert (a==4);
}