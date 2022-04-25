mkdir binary
cd ./code
chmod 755 configure
./configure
make
cd ./BreakID
make clean
make
cd ..
cd ./cnfdedup
make clean
make
cd ..
cd ./saucy
make clean
make
cd ..
cd ..
cp ./code/cryptominisat ./binary/ntusat
cp ./code/saucy/saucy ./binary/saucy
cp ./code/BreakID/BreakID ./binary/BreakID
cp ./code/cnfdedup/cnfdedup ./binary/cnfdedup
cp ./code/removeTseitins.sh ./binary/removeTseitins.sh
cp ./code/runBreakIDntusat.sh ./binary/runBreakIDntusat.sh
chmod 755 ./binary/ntusat 
chmod 755 ./binary/saucy
chmod 755 ./binary/BreakID
chmod 755 ./binary/cnfdedup
chmod 755 ./binary/runBreakIDntusat.sh
chmod 755 ./binary/removeTseitins.sh