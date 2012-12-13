
void main (){
    assert(1==1); //should pass
    assume(0);
    assert(1 == 3); // should not fail since we have assumed false
}
