#CXXFLAGS =	-std=c++0x -g -Wall -fmessage-length=0 -pg
#CXXFLAGS =	-std=c++0x -g -Wall -fmessage-length=0 -pg -DNDEBUG
#CXXFLAGS =	-std=c++0x -O3 -Wall -fmessage-length=0
CXXFLAGS =	-std=c++0x -O3 -Wall -fmessage-length=0 -DNDEBUG -static

OBJS =		Tools.o BreakID.o Symmetry.o SymmetryGroup.o Translator.o

LIBS =

TARGET =	BreakID

$(TARGET):	$(OBJS)
	$(CXX) $(CXXFLAGS) -o $(TARGET) $(OBJS) $(LIBS)

all:	$(TARGET)

clean:
	rm -f $(OBJS) $(TARGET)
