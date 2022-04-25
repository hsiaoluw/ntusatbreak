CXXFLAGS =	-O3 -g -Wall -fmessage-length=0 -std=gnu++11 -static

OBJS =		cnfdedup.o

LIBS =

TARGET =	cnfdedup

$(TARGET):	$(OBJS)
	$(CXX) -o $(TARGET) $(OBJS) $(LIBS)

all:	$(TARGET)

clean:
	rm -f $(OBJS) $(TARGET)
