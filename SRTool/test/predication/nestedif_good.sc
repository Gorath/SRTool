

void main(){
    int x ;
    x = 0;
    if ( x ){

    }else {
        if (x ){

        }else{
          if (x ){

          }else{
            x = 1;
            if (x ){
              x = 3;
            }else{
               x = 4;
            }
          }
        }
    }

    assert ( x == 3);
}
