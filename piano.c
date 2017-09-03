// by：Aug.W.

int ledPin_r = 2;
int ledPin_y = 3;
int ledPin_b = 4;
int capval[7];
//boolean flag_do = false ;
boolean flag_i[7] = {false,false,false,false,false,false,false};
boolean ledPin_Blink_flag = true;
int sum[7] = {0,0,0,0,0,0};
//boolean flag_do = false 




uint8_t readCapacitivePin(int pinToMeasure) {
  pinToMeasure=pinToMeasure+6;
// Variables used to translate from Arduino to AVR pin naming
volatile uint8_t* port;
volatile uint8_t* ddr;
volatile uint8_t* pin;
// Here we translate the input pin number from
// Arduino pin number to the AVR PORT, PIN, DDR,
// and which bit of those registers we care about.
byte bitmask;
port = portOutputRegister(digitalPinToPort(pinToMeasure));
ddr = portModeRegister(digitalPinToPort(pinToMeasure));
bitmask = digitalPinToBitMask(pinToMeasure);
pin = portInputRegister(digitalPinToPort(pinToMeasure));
// Discharge the pin first by setting it low and output
*port &= ~(bitmask);
*ddr |= bitmask;

// Make the pin an input with the internal pull-up on
*ddr &= ~(bitmask);
*port |= bitmask;

// Now see how long the pin to get pulled up. This manual unrolling of the loop
// decreases the number of hardware cycles between each read of the pin,
// thus increasing sensitivity.
uint8_t cycles = 17;
if (*pin & bitmask) { cycles = 0;}
else if (*pin & bitmask) { cycles = 1;}
else if (*pin & bitmask) { cycles = 2;}
else if (*pin & bitmask) { cycles = 3;}
else if (*pin & bitmask) { cycles = 4;}
else if (*pin & bitmask) { cycles = 5;}
else if (*pin & bitmask) { cycles = 6;}
else if (*pin & bitmask) { cycles = 7;}
else if (*pin & bitmask) { cycles = 8;}
else if (*pin & bitmask) { cycles = 9;}
else if (*pin & bitmask) { cycles = 10;}
else if (*pin & bitmask) { cycles = 11;}
else if (*pin & bitmask) { cycles = 12;}
else if (*pin & bitmask) { cycles = 13;}
else if (*pin & bitmask) { cycles = 14;}
else if (*pin & bitmask) { cycles = 15;}
else if (*pin & bitmask) { cycles = 16;}

// Discharge the pin again by setting it low and output
// It's important to leave the pins low if you want to 
// be able to touch more than 1 sensor at a time - if
// the sensor is left pulled high, when you touch
// two sensors, your body will transfer the charge between
// sensors.
*port &= ~(bitmask);
*ddr |= bitmask;
return cycles;
}


int switchSound(int sound){
  int i=sound;
  int j=9;
  int k =capval[i];
   if (capval[i] >2) { 
      if(flag_i[i]){
        flag_i[i] = false ;
        if(capval[i]<5) j =  i;
        else j=i+7;  
      }
    }else{
      sum[i]++;
      if(sum[i]>1){
         flag_i[i] = true ;
         sum[i] = 0;
      }
    }
//    Serial.println(k );
    return j;
}



void setup()
{
  
  pinMode(ledPin_r, OUTPUT);
  pinMode(ledPin_y, OUTPUT);
  pinMode(ledPin_b, OUTPUT);
  Serial.begin(9600);
}

void loop ()
{
    //Serial.println(analog0);
    /*if (ledPin_Blink_flag)
    {
        ledPin_Blink_flag = false;
        digitalWrite(ledPin_r, HIGH);  
        digitalWrite(ledPin_r, LOW);  
        digitalWrite(ledPin_r, HIGH);  
        digitalWrite(ledPin_r, LOW);  
        digitalWrite(ledPin_r, HIGH);   
        digitalWrite(ledPin_r, LOW);   
        digitalWrite(ledPin_r, HIGH);  
        digitalWrite(ledPin_r, LOW);  

        digitalWrite(ledPin_b, HIGH);  
        digitalWrite(ledPin_b, LOW);  
        digitalWrite(ledPin_b, HIGH);  
        digitalWrite(ledPin_b, LOW);  
        digitalWrite(ledPin_b, HIGH);   
        digitalWrite(ledPin_b, LOW);   
        digitalWrite(ledPin_b, HIGH);  
        digitalWrite(ledPin_b, LOW);         

        return;
    }
*/
//byte temp[8]={0xAA,0x1B,0x04,0x30,0x31,0x30,0x32,0x8c};
//Serial.write(temp,8);
  for(int i=0;i<7;i++){
    capval[i] = readCapacitivePin(i);
    // Serial.println(capval[i]);
  }
int list[7];
for(int i=0;i<7;i++){
    list[i]=switchSound(i);
}

    int numofkeys=0;
    byte order[18]={0xAA,0x1B,14,
    0x32,0x31,
    0x32,0x32,
    0x32,0x33,
    0x32,0x34,
    0x32,0x35,
    0x32,0x36,
    0x32,0x37,
    00};
    
    order[0]=0xAA,
    order[1]=0x1B,
    order[2]=14,
    order[3]=0x32,
    order[4]=0x31,
    order[5]=0x32,
    order[6]=0x32,
    order[7]=0x32,
    order[8]=0x33,
    order[9]=0x32,
    order[10]=0x34,
    order[11]=0x32,
    order[12]=0x35,
    order[13]=0x32,
    order[14]=0x36,
    order[15]=0x32,
    order[16]=0x37,
    order[17]=00;


    for (int i=0;i<7;i++){
        if (capval[i]>2){
            numofkeys++;
        }
        }

    if(numofkeys!=0){
            
        for(int i=0;i<7;i++){
            if(capval[i]>2&&list[i]){
                order[2*i+3]=0x30;
            }
            if(capval[i]>4&&list[i]){
                order[2*i+3]=0x31;
            }
        }
        int sm=0;
        for(int i=0;i<17;i++){
            sm+=(int)order[i];
            // Serial.println(order[i]);
        }
        sm=sm&(255);
        order[17]=(byte)sm;
        // Serial.println(order[17]);
            Serial.write(order,18); //声
           
    }
    
}
