
//this test is mainly for looking at the generated z3 input
void main(){
        int x;
        x = 4;
        assert( x == 4);
        assume(0);
        x = 5;
        assert( x == 9);
}