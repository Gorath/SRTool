void main(){

    int a;
    havoc(a);
    assume(a>=0);
    assert(a>=0);

    while (a<10)
        inv(a>=0){
        assert(a>=0);
        a = a + 1;
    }
}

