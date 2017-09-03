// by：Aug.W.

int capval[7];




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



void setup()
{
  
  Serial.begin(9600);
}

void loop ()
{
  delay(30);
  for(int i=0;i<7;i++){
    capval[i] = readCapacitivePin(i);
     Serial.println(capval[i]);
  }
Serial.println("llllllllllllllllllll");
    int numofkeys=0;
    byte order[6]={0xAA,0x1B,02,
    0x32,0x31,
    00};
    

 numofkeys=0;
    for (int i=0;i<7;i++){
        if (capval[i]>4){
            order[4]=0x31+i;
            numofkeys++;
        }
        }

    if(numofkeys!=0){
            
        for(int i=0;i<7;i++){
            if(capval[i]>4){
                order[3]=0x30;
            }
            if(capval[i]>5){
                order[3]=0x31;
            }
        }
        int sm=0;
        sm=0;
        for(int i=0;i<5;i++){
            sm+=(int)order[i];
            // Serial.println(order[i]);
        }
        sm=sm&(255);
        order[5]=(byte)sm;
        // Serial.println(order[17]);
            Serial.write(order,6); //声
    delay(500);       
    }
    
}
