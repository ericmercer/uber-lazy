#!/bin/bash
for FILE in ./*.dot; 
do ID=`echo ${FILE} | sed 's/dot/pdf/'`; 
dot -Tpdf ${FILE} -o ${ID};
done

