# Threshold PRISM
This code is the SageMath implementation of the threshold PRISM signature.

## Requirements
 + [SageMath version 10.7](https://doc.sagemath.org/html/en/installation/index.html)

## How to run
```bash
cd sage-implementation/applications/PRISM
python tPRISM.py [t] [n] [level]
```
For example, when t = 5, n = 7 and level = 1, run as
```bash
python tPRISM.py 5 7 1
```

## References
### Source Codes
 + [KummerIsogenies](https://github.com/mariascrs/KummerIsogenies) : Efficient (3,3)-isogeny on fast Kummer surfaces
 + [Qlapoti](https://github.com/KULeuven-COSIC/Qlapoti)
 + [sqisign_prism_v2](https://github.com/KULeuven-COSIC/sqisign_prism_v2)
 + [LearnToSQI](https://github.com/LearningToSQI/SQISign-SageMath)
### Related Papers
 + [Efficient (3,3)-isogenies on fast Kummer surfaces](https://eprint.iacr.org/2024/144)
 + [Qlapoti: Simple and Efficient Translation of Quaternion Ideals to Isogenies](https://eprint.iacr.org/2025/1604)
 + [PRISM: Simple And Compact Identification and Signatures From Large Prime Degree Isogenies](https://eprint.iacr.org/2025/135)
