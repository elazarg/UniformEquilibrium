"""Exact rank-four order certificates on the two positive-matching matrix families.

Run with Python 3 and its standard library. Each word lists sixteen isolated validation
labels and six observed training dates. An entry i:n in a prior gives word i weight n.
Every gain is measured in units of 1/4**4 on the indicated row-scaled native matrix.
"""
from fractions import Fraction as F
from functools import lru_cache
from itertools import combinations_with_replacement, permutations, product
from math import prod

N = 4
TRAIN = {"e": (0, 2), "f": (1, 3), "x": (0, 1, 2, 3)}

PAIRED = {
    (-1, -1, -1, -1): (
"""13fx1133f221300x02e02e 31f1x13f1202033x02e02e 13fx00331f31122x02e02e
13fx22113f13300x02e02e 13fx31f0231x300122e02e 03f31x3021f12x02e0213e
13fx0022113f133x02e02e 31fx110033f3122x02e02e 31f02x0331f12x02ee0213""",
"""0:239143 1:71739 2:377004 3:229948 4:63391 5:18775
6:442181 0:69905 1:117417 2:65673 7:211183 8:58415 5:35225
1:19952 2:294990 3:400034 8:152568 4:44631 5:87824"""
),
    (-1, -1, -1, 1): (
"""13fx22113f13300x02e02e 13fx33001f21x02e20213e 103fx0331f31122x02e02e
13fx13f022103xe122003e 13fx1133f122300x02e02e 13fx133f0031122x02e02e
13fx0022113f133x02e02e 13fx113300f1223x02e02e""",
"""0:133480 1:48966 2:404582 3:54096 4:228125 5:130751
0:3415 6:497498 2:81463 3:22973 7:394651
0:316029 6:249314 1:196770 2:171613 3:20278 5:45995"""
),
    (-1, 1, -1, -1): (
"""13fx022113f03xe202103e 31fx113f0032x02e02213e 31fx331f1122300x02e02e
031fx22113f3x200e2103e 13fx00331f23112x02e02e 31f3x1122f13300x02e02e
31fx113f2123300x02e02e 312fx113f123300x02e02e 31fx0022113f13x230e02e
312fx110033fx03122e02e""",
"""0:72204 1:16390 2:10007 3:207 4:316114 5:583183 6:1895
1:224880 3:4257 4:138804 7:60230 6:50300 8:416581 9:104948
0:490337 2:224073 3:69424 4:154510 7:26888 5:4189 9:30580"""
),
    (-1, 1, -1, 1): (
"""02ex11220e20033x13f13f 20ex00332e02211x13f13f 02ex22110e20033x13f13f
0e122x20e120033x13f13f 20e02x03e302211x13f13f e3002x032e02211x13f13f
12e20x20e210033x13f13f 12e20x120e20033x13f13f 20ex1133002e02x321f13f
20ex1120e302x13f13203f 02ex002e1132x13f31203f 20ex002e10332x3211f13f
0312ex13002e02x3f3112f 20ex20e133102xf211033f 2e1003x1022ex033f3112f
02ex33002e02211x13f13f""",
"""0:72240 1:55304 2:13690 3:195415 4:293122 5:77321 6:244268 7:48640
8:387587 0:132829 9:74687 1:10581 10:87092 2:392 11:268237 12:16383 13:14620 14:4744 7:2847
8:160166 0:137686 9:20178 1:28518 10:6483 2:115646 3:888 15:269734 12:17080 5:1437 6:4270 13:236684 14:1233"""
),
    (-1, 1, 1, -1): (
"""20ex33011022ex13f3102f 20ex20033e02211x13f13f 20ex11220e20033x13f13f
02ex33110022exf201133f 12e20x20e120033x13f13f 20ex20e33002211x13f13f
012ex1223300ex3f13102f 20ex002e1123x13f13302f 023ex113002e02x321f13f
20ex0112e33002x321f13f 20ex002e0332211x13f13f 20ex0031122ex03321f13f
20ex1133002e02x321f13f""",
"""0:13389 1:456837 2:134919 3:9821 4:181289 5:86261 6:115274 7:2210
0:36544 8:237808 2:141859 9:142009 3:39354 10:151450 11:37575 12:131884 7:81517
0:132806 1:203510 8:5014 2:296688 3:238256 10:14944 6:55028 7:53754"""
),
}

INDEPENDENT = (
"""02ex0022e032311x13f13f 0e02x022e023311x13f13f 12e20x20e200133x13f13f
30e02x022e02311x13f13f 3102e0x02e022x3113f13f 3102ex0022e02x3113f13f
e1220x200e20133x13f13f 02e0x0233e02211x13f13f 02ex33002e02211x13f13f
102e2x0e3300221x13f13f 1230ex3002e0221x13f13f 1302e02x02ex033211f13f
e1220x20e200133x13f13f e3002x022e03211x13f13f 012ex1220e20033x13f13f
02e012xe1220033x13f13f 02ex01122e20033x13f13f 02ex2200e203311x13f13f
12e20x20e120033x13f13f 0e2x33002e02211x13f13f 20ex002e1123x13f03312f
30e02x02e302211x13f13f 30e1022xe120x12033f13f 02ex002e2203311x13f13f
12e002x02e032x3113f13f 1302ex002e2x203113f13f 210e20x02e21033x13f13f
e310022xe0202x3113f13f 02ex0023e302211x13f13f 120e0x032e022x3113f13f
12e002x0e220133x13f13f 12e002x0e23x023113f13f 12e30x002e022x3113f13f
02e120xe01203x1233f13f 02ex112200e03x1233f13f 1302ex10022ex12033f13f
20e012xe01203x1233f13f 20ex011220e2033x13f13f 02e01x1220e3x13f30312f
02e13x13002e02x123f13f 02ex1133002e02x123f13f 20e0x11220e3x01233f13f
20ex011220e3x13f21033f e312200x02ex203113f13f 02ex20e33020211x13f13f
12e2300xe300221x13f13f 21e3002x302ex30211f13f 3102e02x30e0221x13f13f
3102e02xe0202x3113f13f 02e12x200e12033x13f13f 1320ex220e0x032113f13f
3012ex2200e1x12033f13f 02e1230xe3120x13f1203f 02ex20e33002211x13f13f
1302e02xe3120xf021133f 1302ex300122exf211033f 20e30x113022ex13f1203f
20ex220e1130x20133f13f 20ex33001122exf303112f 3012ex1220e2003x13f13f""",
"""0:7183326 1:9916603 2:25203887 3:24333993 4:2193720 5:1028119 6:30140352
7:7808464 0:2221793 8:7775411 1:15359274 9:4295227 10:9017844 2:43800571 11:501052 12:6250 13:9214115
14:19070035 15:8325833 16:5781604 17:9115 1:9017360 18:26868089 3:26171257 4:2605726 12:2142713 13:8268
14:30633242 7:4016595 8:1628893 1:12261165 19:14825139 18:14784860 20:3888977 21:6207599 22:807146 12:7781728 13:3164655
0:23902399 23:4557487 17:459308 24:31764052 25:9009475 26:6226698 4:11922978 5:12142450 6:5753 27:9400
28:22561001 23:1022937 8:5915956 9:3769687 29:20162186 10:203377 30:12175015 31:2807640 32:12267703 25:1057911 4:18039518 27:17070
33:2945317 16:18658828 34:22416058 35:15646837 36:29235443 37:2459212 4:8638305
15:1879976 38:14284658 33:1886968 39:11281416 28:5816755 16:7065248 40:17002208 9:2705812 10:7737766 32:959114 35:12989797 36:5326086 41:5068178 20:2950891 42:2782823 4:262305
0:9068904 23:13572161 17:23021380 24:2908005 2:13971408 11:35217315 25:10753 26:2221740 43:8333
44:9976284 17:8119025 8:23726415 9:1058133 30:305111 45:6448051 32:6891181 11:8073217 25:15435918 46:10110148 47:4151851 48:5696334 27:8333
14:11104540 15:5173874 33:5864219 49:5301701 16:4501807 34:17656338 17:2501308 18:19385234 11:1226571 35:9252596 50:5207424 26:1752348 51:11063706 43:8333
14:3770875 52:13716761 39:9605658 40:9584232 53:2913769 17:1142993 8:7174350 18:8155734 54:2153679 55:13245977 56:7691000 57:3142588 58:6944707 59:10757676"""
)

@lru_cache(None)
def score(word, receiver, direction, skew):
    """Coefficients of the mate reward or the common scale of the two crosses."""
    pattern = "".join(z for z in word if z in TRAIN)
    assert pattern in ("exexff", "fxfxee")
    validation = [0]*4
    training = [0]*4
    prescribed = offer = 0
    observations = []
    for symbol in word:
        if symbol in TRAIN:
            for owner in TRAIN[symbol]:
                training[owner] += 1
            observations.append(offer)
        else:
            donor = int(symbol)
            assert 0 <= donor < 4
            if donor != receiver:
                mate = donor == (receiver ^ 1)
                value = int(mate) if direction == "mate" else (0 if mate else -1+(-1)**donor*skew)
                mass = value*prod(N-validation[k] for k in range(4) if k not in (receiver, donor))
                prescribed += (N-validation[receiver])*mass
                offer += N*mass
            validation[donor] += 1
        assert all(abs(a-b) <= 1 for a,b in zip(training,validation))
    assert training == validation == [N]*4
    return tuple(prescribed-u for u in observations+[offer])


def check(packet, vertices, directions):
    words = packet[0].split()
    assert len({"".join(c for c in w if c in TRAIN) for w in words}) == 1
    priors = []
    for line in packet[1].splitlines():
        prior = []
        for term in line.split():
            index, weight = map(int, term.split(":"))
            assert 0 <= index < len(words) and weight > 0
            prior.append((words[index],weight))
        total = sum(weight for _,weight in prior)
        priors.append([(word,F(w,total)) for word,w in prior])
    assert len(priors) == len(vertices)
    gains = []
    for row in range(4):
        for d in directions[row]:
            means = []
            for prior in priors:
                means.append([[sum(prob*score(w,row,mode,d)[cut] for w,prob in prior)
                               for mode in ("mate","cross")] for cut in range(7)])
            for j,k in combinations_with_replacement(range(len(vertices)),2):
                for cut in range(7):
                    value = 0
                    for donor,target in ((j,k),(k,j)):
                        mate, cross = vertices[target][row]
                        m, c = means[donor][cut]
                        value += mate*m + cross*c
                    gains.append(value/2)
    assert min(gains) >= 0
    print(f"{len(words)} words, {len(priors)} priors, {len(gains)} Bernstein coefficients,"
          f" {gains.count(0)} equalities, smallest positive {min(x for x in gains if x>0)}.")


def main():
    paired = []
    for x,y in ((F(1,8),F(1,8)), (F(3,8),F(1,8)), (F(1,4),F(1,4))):
        paired.append([(1-2*t,t) for t in (x,x,y,y)])
    # Only within-pair relabelings preserve the selected ordering of the pair ratios.
    permitted = [p for p in permutations(range(4)) if all(p[i]//2 == i//2 for i in range(4))]
    def relabel(signs,p):
        return tuple(signs[p[i]]*(-1 if (p[i^2]-(i^2))%2 else 1) for i in range(4))
    representatives = {min(relabel(d,p) for p in permitted) for d in product((-1,1),repeat=4)}
    assert representatives == set(PAIRED)
    for signs,packet in PAIRED.items():
        # "score" uses the signed cross entry -1+d*(-1)^donor.
        check(packet, paired, [(0,-s) for s in signs])
    delta = F(1,32)
    c = 1/(1-delta)
    top = 3*c/(3*c+1)
    independent = []
    for x,y in ((top,top), (1-top,top), (F(1,2),F(1,2))):
        for qa,qb in product((0,F(1,2)),repeat=2):
            a, b = c*(1-x), c*(1-y)
            independent.append([(x,qa*a),(x,(1-qa)*a),(y,qb*b),(y,(1-qb)*b)])
    check(INDEPENDENT, independent, [(-delta,delta)]*4)


if __name__ == "__main__":
    main()
