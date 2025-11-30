use crate::algebraic::Factor::{AddSub, Numeric};
use crate::{MAX_ID_EQUAL_TO_VALUE, write_bignum};
use const_format::formatcp;
use hipstr::HipStr;
use itertools::Itertools;
use log::{debug, error, info, warn};
use num_integer::Integer;
use num_modular::ModularPow;
use num_prime::ExactRoots;
use num_prime::Primality::No;
use num_prime::buffer::{NaiveBuffer, PrimeBufferExt};
use num_prime::detail::SMALL_PRIMES;
use num_prime::nt_funcs::factorize128;
use regex::{Regex, RegexSet};
use std::cmp::{Ordering, PartialEq};
use std::collections::{BTreeMap, VecDeque};
use std::f64::consts::LN_10;
use std::f64::consts::LOG10_2;
use std::fmt::{Display, Formatter};
use std::hash::Hash;
use std::hint::unreachable_unchecked;
use std::iter::repeat_n;
use std::mem::{swap, take};

static SMALL_FIBONACCI_FACTORS: [&[u128]; 199] = [
    &[0],
    &[],
    &[],
    &[2],
    &[3],
    &[5],
    &[2, 2, 2],
    &[13],
    &[3, 7],
    &[2, 17],
    &[5, 11],
    &[89],
    &[2, 2, 2, 2, 3, 3],
    &[233],
    &[13, 29],
    &[2, 5, 61],
    &[3, 7, 47],
    &[1597],
    &[2, 2, 2, 17, 19],
    &[37, 113],
    &[3, 5, 11, 41],
    &[2, 13, 421],
    &[89, 199],
    &[28657],
    &[2, 2, 2, 2, 2, 3, 3, 7, 23],
    &[5, 5, 3001],
    &[233, 521],
    &[2, 17, 53, 109],
    &[3, 13, 29, 281],
    &[514229],
    &[2, 2, 2, 5, 11, 31, 61],
    &[557, 2417],
    &[3, 7, 47, 2207],
    &[2, 89, 19801],
    &[1597, 3571],
    &[5, 13, 141961],
    &[2, 2, 2, 2, 3, 3, 3, 17, 19, 107],
    &[73, 149, 2221],
    &[37, 113, 9349],
    &[2, 233, 135721],
    &[3, 5, 7, 11, 41, 2161],
    &[2789, 59369],
    &[2, 2, 2, 13, 29, 211, 421],
    &[433494437],
    &[3, 43, 89, 199, 307],
    &[2, 5, 17, 61, 109441],
    &[139, 461, 28657],
    &[2971215073],
    &[2, 2, 2, 2, 2, 2, 3, 3, 7, 23, 47, 1103],
    &[13, 97, 6168709],
    &[5, 5, 11, 101, 151, 3001],
    &[2, 1597, 6376021],
    &[3, 233, 521, 90481],
    &[953, 55945741],
    &[2, 2, 2, 17, 19, 53, 109, 5779],
    &[5, 89, 661, 474541],
    &[3, 7, 7, 13, 29, 281, 14503],
    &[2, 37, 113, 797, 54833],
    &[59, 19489, 514229],
    &[353, 2710260697],
    &[2, 2, 2, 2, 3, 3, 5, 11, 31, 41, 61, 2521],
    &[4513, 555003497],
    &[557, 2417, 3010349],
    &[2, 13, 17, 421, 35239681],
    &[3, 7, 47, 1087, 2207, 4481],
    &[5, 233, 14736206161],
    &[2, 2, 2, 89, 199, 9901, 19801],
    &[269, 116849, 1429913],
    &[3, 67, 1597, 3571, 63443],
    &[2, 137, 829, 18077, 28657],
    &[5, 11, 13, 29, 71, 911, 141961],
    &[6673, 46165371073],
    &[2, 2, 2, 2, 2, 3, 3, 3, 7, 17, 19, 23, 107, 103681],
    &[9375829, 86020717],
    &[73, 149, 2221, 54018521],
    &[2, 5, 5, 61, 3001, 230686501],
    &[3, 37, 113, 9349, 29134601],
    &[13, 89, 988681, 4832521],
    &[2, 2, 2, 79, 233, 521, 859, 135721],
    &[157, 92180471494753],
    &[3, 5, 7, 11, 41, 47, 1601, 2161, 3041],
    &[2, 17, 53, 109, 2269, 4373, 19441],
    &[2789, 59369, 370248451],
    &[99194853094755497],
    &[2, 2, 2, 2, 3, 3, 13, 29, 83, 211, 281, 421, 1427],
    &[5, 1597, 9521, 3415914041],
    &[6709, 144481, 433494437],
    &[2, 173, 514229, 3821263937],
    &[3, 7, 43, 89, 199, 263, 307, 881, 967],
    &[1069, 1665088321800481],
    &[2, 2, 2, 5, 11, 17, 19, 31, 61, 181, 541, 109441],
    &[13, 13, 233, 741469, 159607993],
    &[3, 139, 461, 4969, 28657, 275449],
    &[2, 557, 2417, 4531100550901],
    &[2971215073, 6643838879],
    &[5, 37, 113, 761, 29641, 67735001],
    &[2, 2, 2, 2, 2, 2, 2, 3, 3, 7, 23, 47, 769, 1103, 2207, 3167],
    &[193, 389, 3084989, 361040209],
    &[13, 29, 97, 6168709, 599786069],
    &[2, 17, 89, 197, 19801, 18546805133],
    &[3, 5, 5, 11, 41, 101, 151, 401, 3001, 570601],
    &[743519377, 770857978613],
    &[2, 2, 2, 919, 1597, 3469, 3571, 6376021],
    &[519121, 5644193, 512119709],
    &[3, 7, 103, 233, 521, 90481, 102193207],
    &[2, 5, 13, 61, 421, 141961, 8288823481],
    &[953, 55945741, 119218851371],
    &[1247833, 8242065050061761],
    &[2, 2, 2, 2, 3, 3, 3, 3, 17, 19, 53, 107, 109, 5779, 11128427],
    &[827728777, 32529675488417],
    &[5, 11, 11, 89, 199, 331, 661, 39161, 474541],
    &[2, 73, 149, 2221, 1459000305513721],
    &[3, 7, 7, 13, 29, 47, 281, 14503, 10745088481],
    &[677, 272602401466814027129],
    &[2, 2, 2, 37, 113, 229, 797, 9349, 54833, 95419],
    &[5, 1381, 28657, 2441738887963981],
    &[3, 59, 347, 19489, 514229, 1270083883],
    &[2, 17, 233, 29717, 135721, 39589685693],
    &[353, 709, 8969, 336419, 2710260697],
    &[13, 1597, 159512939815855788121],
    &[
        2, 2, 2, 2, 2, 3, 3, 5, 7, 11, 23, 31, 41, 61, 241, 2161, 2521, 20641,
    ],
    &[89, 97415813466381445596089],
    &[4513, 555003497, 5600748293801],
    &[2, 2789, 59369, 68541957733949701],
    &[3, 557, 2417, 3010349, 3020733700601],
    &[5, 5, 5, 3001, 158414167964045700001],
    &[2, 2, 2, 13, 17, 19, 29, 211, 421, 1009, 31249, 35239681],
    &[27941, 5568053048227732210073],
    &[3, 7, 47, 127, 1087, 2207, 4481, 186812208641],
    &[2, 257, 5417, 8513, 39639893, 433494437],
    &[5, 11, 131, 233, 521, 2081, 24571, 14736206161],
    &[1066340417491710595814572169],
    &[2, 2, 2, 2, 3, 3, 43, 89, 199, 307, 9901, 19801, 261399601],
    &[13, 37, 113, 3457, 42293, 351301301942501],
    &[269, 4021, 116849, 1429913, 24994118449],
    &[2, 5, 17, 53, 61, 109, 109441, 1114769954367361],
    &[3, 7, 67, 1597, 3571, 63443, 23230657239121],
    &[19134702400093278081449423917],
    &[2, 2, 2, 137, 139, 461, 691, 829, 18077, 28657, 1485571],
    &[277, 2114537501, 85526722937689093],
    &[3, 5, 11, 13, 29, 41, 71, 281, 911, 141961, 12317523121],
    &[2, 108289, 1435097, 142017737, 2971215073],
    &[6673, 46165371073, 688846502588399],
    &[89, 233, 8581, 1929584153756850496621],
    &[
        2,
        2,
        2,
        2,
        2,
        2,
        3,
        3,
        3,
        7,
        17,
        19,
        23,
        47,
        107,
        1103,
        103681,
        10749957121,
    ],
    &[5, 514229, 349619996930737079890201],
    &[151549, 9375829, 86020717, 11899937029],
    &[2, 13, 97, 293, 421, 3529, 6168709, 347502052673],
    &[3, 73, 149, 2221, 11987, 54018521, 81143477963],
    &[110557, 162709, 4000949, 85607646594577],
    &[
        2, 2, 2, 5, 5, 11, 31, 61, 101, 151, 3001, 12301, 18451, 230686501,
    ],
    &[5737, 2811666624525811646469915877],
    &[3, 7, 37, 113, 9349, 29134601, 1091346396980401],
    &[2, 17, 17, 1597, 6376021, 7175323114950564593],
    &[13, 29, 89, 199, 229769, 988681, 4832521, 9321929],
    &[5, 557, 2417, 21701, 12370533881, 61182778621],
    &[
        2,
        2,
        2,
        2,
        3,
        3,
        79,
        233,
        521,
        859,
        90481,
        135721,
        12280217041,
    ],
    &[313, 11617, 7636481, 10424204306491346737],
    &[157, 92180471494753, 32361122672259149],
    &[2, 317, 953, 55945741, 97639037, 229602768949],
    &[3, 5, 7, 11, 41, 47, 1601, 2161, 2207, 3041, 23725145626561],
    &[13, 8693, 28657, 612606107755058997065597],
    &[
        2, 2, 2, 17, 19, 53, 109, 2269, 3079, 4373, 5779, 19441, 62650261,
    ],
    &[977, 4892609, 33365519393, 32566223208133],
    &[3, 163, 2789, 59369, 800483, 350207569, 370248451],
    &[2, 5, 61, 89, 661, 19801, 86461, 474541, 518101, 900241],
    &[35761381, 6202401259, 99194853094755497],
    &[18104700793, 1966344318693345608565721],
    &[
        2, 2, 2, 2, 2, 3, 3, 7, 7, 13, 23, 29, 83, 167, 211, 281, 421, 1427, 14503, 65740583,
    ],
    &[233, 337, 89909, 104600155609, 126213229732669],
    &[5, 11, 1597, 3571, 9521, 1158551, 12760031, 3415914041],
    &[2, 17, 37, 113, 797, 6841, 54833, 5741461760879844361],
    &[3, 6709, 144481, 433494437, 313195711516578281],
    &[1639343785721, 389678749007629271532733],
    &[2, 2, 2, 59, 173, 349, 19489, 514229, 947104099, 3821263937],
    &[5, 5, 13, 701, 3001, 141961, 17231203730201189308301],
    &[
        3, 7, 43, 47, 89, 199, 263, 307, 881, 967, 93058241, 562418561,
    ],
    &[2, 353, 2191261, 805134061, 1297027681, 2710260697],
    &[179, 1069, 1665088321800481, 22235502640988369],
    &[21481, 156089, 3418816640903898929534613769],
    &[
        2,
        2,
        2,
        2,
        3,
        3,
        3,
        5,
        11,
        17,
        19,
        31,
        41,
        61,
        107,
        181,
        541,
        2521,
        109441,
        10783342081,
    ],
    &[8689, 422453, 8175789237238547574551461093],
    &[13, 13, 29, 233, 521, 741469, 159607993, 689667151970161],
    &[2, 1097, 4513, 555003497, 14297347971975757800833],
    &[3, 7, 139, 461, 4969, 28657, 253367, 275449, 9506372193863],
    &[5, 73, 149, 2221, 1702945513191305556907097618161],
    &[2, 2, 2, 557, 2417, 63799, 3010349, 35510749, 4531100550901],
    &[89, 373, 1597, 10157807305963434099105034917037],
    &[3, 563, 5641, 2971215073, 6643838879, 4632894751907],
    &[2, 13, 17, 53, 109, 421, 38933, 35239681, 955921950316735037],
    &[
        5, 11, 37, 113, 191, 761, 9349, 29641, 41611, 67735001, 87382901,
    ],
    &[4870723671313, 757810806256989128439975793],
    &[
        2,
        2,
        2,
        2,
        2,
        2,
        2,
        2,
        3,
        3,
        7,
        23,
        47,
        769,
        1087,
        1103,
        2207,
        3167,
        4481,
        11862575248703,
    ],
    &[9465278929, 1020930432032326933976826008497],
    &[193, 389, 3299, 3084989, 361040209, 56678557502141579],
    &[2, 5, 61, 233, 135721, 14736206161, 88999250837499877681],
    &[3, 13, 29, 97, 281, 5881, 6168709, 599786069, 61025309469041],
    &[15761, 25795969, 227150265697, 717185107125886549],
    &[
        2,
        2,
        2,
        17,
        19,
        89,
        197,
        199,
        991,
        2179,
        9901,
        19801,
        1513909,
        18546805133,
    ],
];

static SMALL_LUCAS_FACTORS: [&[u128]; 202] = [
    &[2],
    &[],
    &[3],
    &[2, 2],
    &[7],
    &[11],
    &[2, 3, 3],
    &[29],
    &[47],
    &[2, 2, 19],
    &[3, 41],
    &[199],
    &[2, 7, 23],
    &[521],
    &[3, 281],
    &[2, 2, 11, 31],
    &[2207],
    &[3571],
    &[2, 3, 3, 3, 107],
    &[9349],
    &[7, 2161],
    &[2, 2, 29, 211],
    &[3, 43, 307],
    &[139, 461],
    &[2, 47, 1103],
    &[11, 101, 151],
    &[3, 90481],
    &[2, 2, 19, 5779],
    &[7, 7, 14503],
    &[59, 19489],
    &[2, 3, 3, 41, 2521],
    &[3010349],
    &[1087, 4481],
    &[2, 2, 199, 9901],
    &[3, 67, 63443],
    &[11, 29, 71, 911],
    &[2, 7, 23, 103681],
    &[54018521],
    &[3, 29134601],
    &[2, 2, 79, 521, 859],
    &[47, 1601, 3041],
    &[370248451],
    &[2, 3, 3, 83, 281, 1427],
    &[6709, 144481],
    &[7, 263, 881, 967],
    &[2, 2, 11, 19, 31, 181, 541],
    &[3, 4969, 275449],
    &[6643838879],
    &[2, 769, 2207, 3167],
    &[29, 599786069],
    &[3, 41, 401, 570601],
    &[2, 2, 919, 3469, 3571],
    &[7, 103, 102193207],
    &[119218851371],
    &[2, 3, 3, 3, 3, 107, 11128427],
    &[11, 11, 199, 331, 39161],
    &[47, 10745088481],
    &[2, 2, 229, 9349, 95419],
    &[3, 347, 1270083883],
    &[709, 8969, 336419],
    &[2, 7, 23, 241, 2161, 20641],
    &[5600748293801],
    &[3, 3020733700601],
    &[2, 2, 19, 29, 211, 1009, 31249],
    &[127, 186812208641],
    &[11, 131, 521, 2081, 24571],
    &[2, 3, 3, 43, 307, 261399601],
    &[4021, 24994118449],
    &[7, 23230657239121],
    &[2, 2, 139, 461, 691, 1485571],
    &[3, 41, 281, 12317523121],
    &[688846502588399],
    &[2, 47, 1103, 10749957121],
    &[151549, 11899937029],
    &[3, 11987, 81143477963],
    &[2, 2, 11, 31, 101, 151, 12301, 18451],
    &[7, 1091346396980401],
    &[29, 199, 229769, 9321929],
    &[2, 3, 3, 90481, 12280217041],
    &[32361122672259149],
    &[2207, 23725145626561],
    &[2, 2, 19, 3079, 5779, 62650261],
    &[3, 163, 800483, 350207569],
    &[35761381, 6202401259],
    &[2, 7, 7, 23, 167, 14503, 65740583],
    &[11, 3571, 1158551, 12760031],
    &[3, 313195711516578281],
    &[2, 2, 59, 349, 19489, 947104099],
    &[47, 93058241, 562418561],
    &[179, 22235502640988369],
    &[2, 3, 3, 3, 41, 107, 2521, 10783342081],
    &[29, 521, 689667151970161],
    &[7, 253367, 9506372193863],
    &[2, 2, 63799, 3010349, 35510749],
    &[3, 563, 5641, 4632894751907],
    &[11, 191, 9349, 41611, 87382901],
    &[2, 1087, 4481, 11862575248703],
    &[3299, 56678557502141579],
    &[3, 281, 5881, 61025309469041],
    &[2, 2, 19, 199, 991, 2179, 9901, 1513909],
    &[7, 2161, 9125201, 5738108801],
    &[809, 7879, 201062946718741],
    &[2, 3, 3, 67, 409, 63443, 66265118449],
    &[619, 1031, 5257480026438961],
    &[47, 3329, 106513889, 325759201],
    &[2, 2, 11, 29, 31, 71, 211, 911, 21211, 767131],
    &[3, 1483, 2969, 1076012367720403],
    &[47927441, 479836483312919],
    &[2, 7, 23, 6263, 103681, 177962167367],
    &[128621, 788071, 593985111211],
    &[3, 41, 43, 307, 59996854928656801],
    &[2, 2, 4441, 146521, 1121101, 54018521],
    &[223, 449, 2207, 1154149773784223],
    &[412670427844921037470771],
    &[2, 3, 3, 227, 26449, 29134601, 212067587],
    &[11, 139, 461, 1151, 5981, 324301, 686551],
    &[7, 299281, 834428410879506721],
    &[2, 2, 19, 79, 521, 859, 1052645985555841],
    &[3, 15247723, 100049587197598387],
    &[29, 239, 3571, 10711, 27932732439809],
    &[2, 47, 1103, 1601, 3041, 23735900452321],
    &[199, 97420733208491869044199],
    &[3, 19763, 21291929, 24848660119363],
    &[2, 2, 4767481, 370248451, 7188487771],
    &[7, 743, 467729, 33758740830460183],
    &[11, 101, 151, 251, 112128001, 28143378001],
    &[2, 3, 3, 3, 83, 107, 281, 1427, 1461601, 764940961],
    &[509, 5081, 487681, 13822681, 19954241],
    &[119809, 4698167634523379875583],
    &[2, 2, 6709, 144481, 308311, 761882591401],
    &[3, 41, 3121, 90481, 42426476041450801],
    &[1049, 414988698461, 5477332620091],
    &[2, 7, 23, 263, 881, 967, 5281, 66529, 152204449],
    &[29, 9349, 10694421739, 2152958650459],
    &[3, 6163, 201912469249, 2705622682163],
    &[2, 2, 11, 19, 31, 181, 271, 541, 811, 5779, 42391, 119611],
    &[47, 562627837283291940137654881],
    &[541721291, 78982487870939058281],
    &[2, 3, 3, 4969, 16561, 162563, 275449, 1043766587],
    &[30859, 253279129, 14331800109223159],
    &[7, 7, 2161, 14503, 118021448662479038881],
    &[2, 2, 79099591, 6643838879, 139509555271],
    &[3, 283, 569, 2820403, 9799987, 35537616083],
    &[199, 521, 1957099, 2120119, 1784714380021],
    &[2, 769, 2207, 3167, 115561578124838522881],
    &[11, 59, 19489, 120196353941, 1322154751061],
    &[3, 29201, 37125857850184727260788881],
    &[2, 2, 29, 211, 65269, 620929, 8844991, 599786069],
    &[7, 10661921, 114087288048701953998401],
    &[952111, 4434539, 3263039535803245519],
    &[2, 3, 3, 41, 401, 601, 2521, 570601, 87129547172401],
    &[1511, 109734721, 217533000184835774779],
    &[47, 562766385967, 2206456200865197103],
    &[2, 2, 19, 919, 3469, 3571, 13159, 8293976826829399],
    &[3, 43, 281, 307, 15252467, 900164950225760603],
    &[11, 311, 3010349, 29138888651, 823837075741],
    &[2, 7, 23, 103, 1249, 102193207, 94491842183551489],
    &[39980051, 16188856575286517818849171],
    &[3, 21803, 5924683, 14629892449, 184715524801],
    &[2, 2, 785461, 119218851371, 4523819299182451],
    &[641, 1087, 4481, 878132240443974874201601],
    &[29, 139, 461, 1289, 1917511, 965840862268529759],
    &[2, 3, 3, 3, 3, 3, 107, 11128427, 1828620361, 6782976947987],
    &[1043201, 6601501, 1686454671192230445929],
    &[7, 2684571411430027028247905903965201],
    &[
        2, 2, 11, 11, 31, 199, 331, 9901, 39161, 51164521, 1550853481,
    ],
    &[3, 6464041, 245329617161, 10341247759646081],
    &[766531, 103849927693584542320127327909],
    &[2, 47, 1103, 10745088481, 115613939510481515041],
    &[521, 596107814364089, 671040394220849329],
    &[3, 41, 67, 1361, 40801, 63443, 11614654211954032961],
    &[2, 2, 19, 19, 229, 9349, 95419, 162451, 1617661, 7038398989],
    &[7, 126117711915911646784404045944033521],
    &[78889, 6248069, 16923049609, 171246170261359],
    &[2, 3, 3, 347, 97787, 528295667, 1270083883, 5639710969],
    &[11, 29, 71, 101, 151, 911, 54601, 560701, 7517651, 51636551],
    &[1409, 2207, 6086461133983, 319702847642258783],
    &[2, 2, 709, 8969, 336419, 10884439, 105117617351706859],
    &[3, 5280544535667472291277149119296546201],
    &[359, 1066737847220321, 66932254279484647441],
    &[2, 7, 23, 241, 2161, 8641, 20641, 103681, 13373763765986881],
    &[97379, 21373261504197751, 32242356485644069],
    &[3, 281, 90481, 232961, 6110578634294886534808481],
    &[2, 2, 14686239709, 5600748293801, 533975715909289],
    &[47, 367, 37309023160481, 441720958100381917103],
    &[11, 54018521, 265272771839851, 2918000731816531],
    &[2, 3, 3, 15917507, 3020733700601, 859886421593527043],
    &[199, 1871, 3571, 905674234408506526265097390431],
    &[7, 18049, 100769, 153037630649666194962091443041],
    &[
        2, 2, 19, 29, 211, 379, 1009, 5779, 31249, 85429, 912871, 1258740001,
    ],
    &[3, 41, 2281, 4561, 29134601, 782747561, 174795553490801],
    &[22921, 395586472506832921, 910257559954057439],
    &[2, 127, 383, 5662847, 6803327, 19073614849, 186812208641],
    &[303011, 76225351, 935527893146187207403151261],
    &[3, 195163, 4501963, 5644065667, 2350117027000544947],
    &[
        2, 2, 11, 31, 79, 131, 521, 859, 1951, 2081, 2731, 24571, 866581, 37928281,
    ],
    &[7, 7, 7, 14503, 3016049, 6100804791163473872231629367],
    &[31498587119111339, 4701907222895068350249889],
    &[
        2,
        3,
        3,
        3,
        43,
        107,
        307,
        261399601,
        11166702227,
        1076312899454363,
    ],
    &[2389, 4503769, 36036960414811969810787847118289],
    &[47, 1601, 3041, 124001, 6996001, 3160438834174817356001],
    &[2, 2, 4021, 24994118449, 2686039424221, 940094299967491],
];

#[derive(Clone, Debug, Hash, Eq, PartialEq)]
pub enum Factor {
    Numeric(u128),
    BigNumber(HipStr<'static>),
    ElidedNumber(HipStr<'static>),
    UnknownExpression(HipStr<'static>),
    AddSub {
        left: Box<Factor>,
        right: Box<Factor>,
        subtract: bool,
    },
    Multiply {
        terms: Vec<Factor>,
    },
    Divide {
        left: Box<Factor>,
        right: Vec<Factor>,
    },
    Power {
        base: Box<Factor>,
        exponent: Box<Factor>,
    },
    Fibonacci(Box<Factor>),
    Lucas(Box<Factor>),
    Factorial(Box<Factor>),
    Primorial(Box<Factor>),
}

impl Default for Factor {
    fn default() -> Self {
        Numeric(1)
    }
}

peg::parser! {
  pub grammar expression_parser() for str {
    pub rule number() -> Factor
      = n:$(['0'..='9']+) { n.parse::<u128>().map(Factor::Numeric).unwrap_or_else(|_| Factor::BigNumber(n.into())) }

    pub rule muldiv_term() -> Factor = precedence!{
      x:@ "^" y:(@) { Factor::Power { base: x.into(), exponent: y.into() } }
      --
      x:@ "!" { Factor::Factorial(x.into()) }
      x:@ "#" { Factor::Primorial(x.into()) }
      --
      "I" x:@ { Factor::Fibonacci(x.into()) }
      --
      "lucas(" x:arithmetic() ")" { Factor::Lucas(x.into()) }
      --
      n:number() { n }
      --
      n:$(['0'..='9']+ ".." ['0'..='9']+) { Factor::ElidedNumber(n.into()) }
      --
      "(" e:arithmetic() ")" { e }
    }

    pub rule div_term() -> Factor = precedence!{
        x:(muldiv_term() **<2,> "*") { Factor::Multiply { terms: x } }
        --
        x:muldiv_term() { x }
    }

    #[cache_left_rec]
    pub rule arithmetic() -> Factor = precedence!{
      x:(@) "+" y:@ { Factor::AddSub { left: x.into(), right: y.into(), subtract: false } }
      x:(@) "-" y:@ { Factor::AddSub { left: x.into(), right: y.into(), subtract: true } }
      --
      x:(div_term()) "/" y:(div_term() ++ "/") { let mut x = x;
        if let Factor::Divide { ref mut right, .. } = x {
            right.extend(y.into_iter());
            x
        } else {
            Factor::Divide { left: x.into(), right: y }
        }
      }
      --
      x:div_term() { x }
    }
  }
}

impl Factor {
    #[inline(always)]
    pub fn known_id(&self) -> Option<u128> {
        if let Numeric(n) = self
            && *n <= MAX_ID_EQUAL_TO_VALUE
        {
            Some(*n)
        } else {
            None
        }
    }
    #[inline(always)]
    pub fn as_u128(&self) -> Option<u128> {
        match self {
            Numeric(n) => Some(*n),
            _ => None,
        }
    }

    #[inline(always)]
    pub fn as_str(&self) -> HipStr<'static> {
        match self {
            Numeric(n) => n.to_string().into(),
            Factor::BigNumber(s) => s.clone(),
            _ => self.to_string().into(),
        }
    }

    #[inline(always)]
    pub fn as_str_non_u128(&self) -> Option<HipStr<'static>> {
        match self {
            Numeric(_) => None,
            Factor::BigNumber(n) => Some(n.clone()),
            _ => Some(self.to_string().into()),
        }
    }

    fn muldiv_depth(&self, max: usize) -> usize {
        if max == 0 {
            return 0;
        }
        match self {
            Factor::Multiply { terms } => {
                1 + terms
                    .iter()
                    .map(|term| term.muldiv_depth(max - 1))
                    .max()
                    .unwrap_or(0)
            }
            Factor::Divide { left, right } => {
                1 + right
                    .iter()
                    .map(|term| term.muldiv_depth(max - 1))
                    .max()
                    .unwrap_or(0)
                    .max(left.muldiv_depth(max - 1))
            }
            _ => 0,
        }
    }

    #[inline(always)]
    fn flatten(self, max_depth: usize) -> Factor {
        let depth = self.muldiv_depth(max_depth);
        if depth < max_depth {
            return self;
        }
        match self {
            Factor::Divide {
                mut left,
                mut right,
            } => {
                while let Factor::Divide {
                    left: left_left,
                    right: mut mid,
                } = *left
                {
                    mid.extend(right.into_iter());
                    right = mid;
                    left = left_left;
                }
                Factor::Divide { left, right }
            }
            Factor::Multiply { terms } => {
                let mut flattened_terms = Vec::with_capacity(terms.len() + depth);
                let mut new_terms = VecDeque::from(terms);
                new_terms.reserve(depth);
                while let Some(new_term) = new_terms.pop_front() {
                    match new_term {
                        Factor::Multiply { terms } => new_terms.extend_front(terms),
                        _ => flattened_terms.push(new_term),
                    }
                }
                Factor::Multiply {
                    terms: flattened_terms,
                }
            }
            _ => self,
        }
    }

    #[inline(always)]
    fn last_digit(&self) -> Option<u8> {
        match self {
            Factor::BigNumber(n) | Factor::ElidedNumber(n) => {
                Some(n.chars().last().unwrap().to_digit(10).unwrap() as u8)
            }
            Numeric(n) => Some((n % 10) as u8),
            _ => None,
        }
    }

    #[inline]
    pub fn may_be_proper_divisor_of(&self, other: &Factor) -> bool {
        if let Numeric(n) = self
            && let Numeric(o) = other
        {
            return o > n && o.is_multiple_of(n);
        };
        if let Factor::BigNumber(_) = self {
            match other {
                Numeric(_) => return false,
                Factor::BigNumber(_) => {
                    if self > other {
                        return false;
                    }
                }
                _ => {}
            }
        }
        if self == other {
            return false;
        }
        if let Factor::Divide { left, .. } = other
            && !self.may_be_proper_divisor_of(left)
        {
            return false;
        }
        let Some(last_digit) = self.last_digit() else {
            return true;
        };
        let Some(other_last_digit) = other.last_digit() else {
            return true;
        };
        match last_digit {
            0 => vec![0],
            2 | 4 | 6 | 8 => vec![0, 2, 4, 6, 8],
            5 => vec![0, 5],
            1 | 3 | 7 | 9 => vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9],
            _ => unsafe { unreachable_unchecked() },
        }
        .contains(&other_last_digit)
    }
}

impl From<u128> for Factor {
    #[inline(always)]
    fn from(value: u128) -> Self {
        Numeric(value)
    }
}

macro_rules! factor_from_str {
    ($type:ty) => {
        impl From<$type> for Factor {
            #[inline(always)]
            fn from(value: $type) -> Self {
                expression_parser::arithmetic(value.as_str())
                    .map(|factor| *Box::new(factor.flatten(2)))
                    .unwrap_or_else(|_| Factor::UnknownExpression(value.into()))
            }
        }
    };
}

factor_from_str!(&str);
factor_from_str!(String);
factor_from_str!(HipStr<'static>);

impl Display for Factor {
    #[inline(always)]
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Numeric(n) => n.fmt(f),
            Factor::BigNumber(s) => write_bignum(f, s),
            Factor::UnknownExpression(e) => e.fmt(f),
            Factor::ElidedNumber(e) => e.fmt(f),
            Factor::AddSub {
                left,
                right,
                subtract,
            } => f.write_fmt(format_args!(
                "({left}{}{right})",
                if *subtract { '-' } else { '+' }
            )),
            Factor::Multiply { terms } => f.write_fmt(format_args!("({})", terms.iter().join("*"))),
            Factor::Divide { left, right } => {
                f.write_fmt(format_args!("({left}/{})", right.iter().join("/")))
            }
            Factor::Power { base, exponent } => f.write_fmt(format_args!("({base})^({exponent})")),
            Factor::Factorial(input) => f.write_fmt(format_args!("({input}!)")),
            Factor::Primorial(input) => f.write_fmt(format_args!("({input}#)")),
            Factor::Fibonacci(input) => f.write_fmt(format_args!("I({input})")),
            Factor::Lucas(input) => f.write_fmt(format_args!("lucas({input})")),
        }
    }
}

impl PartialOrd<Factor> for Factor {
    #[inline(always)]
    fn partial_cmp(&self, other: &Factor) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Factor {
    #[inline(always)]
    fn cmp(&self, other: &Self) -> Ordering {
        match self {
            Numeric(n) => match other {
                Numeric(o) => n.cmp(o),
                Factor::BigNumber(_) => Ordering::Less,
                _ => Ordering::Less,
            },
            Factor::BigNumber(s) => match other {
                Numeric(_) => Ordering::Greater,
                Factor::BigNumber(o) => s.len().cmp(&o.len()).then_with(|| s.cmp(o)),
                _ => Ordering::Less,
            },
            _ => match other {
                Numeric(_) => Ordering::Greater,
                Factor::BigNumber(_) => Ordering::Greater,
                _ => {
                    let s = self.to_string();
                    let o = other.to_string();
                    s.len().cmp(&o.len()).then_with(|| s.cmp(&o))
                }
            },
        }
    }
}

pub struct FactorFinder {
    regexes: Box<[Regex]>,
    regexes_as_set: RegexSet,
    sieve: NaiveBuffer,
}

impl Clone for FactorFinder {
    #[inline(always)]
    fn clone(&self) -> Self {
        FactorFinder {
            regexes: self.regexes.clone(),
            regexes_as_set: self.regexes_as_set.clone(),
            sieve: NaiveBuffer::new(),
        }
    }

    #[inline(always)]
    fn clone_from(&mut self, _source: &Self) {
        // No-op because all instances are interchangeables
    }
}

#[inline(always)]
fn count_frequencies<T: Eq + Ord>(vec: Vec<T>) -> BTreeMap<T, usize> {
    let mut counts = BTreeMap::new();
    for item in vec {
        *counts.entry(item).or_insert(0) += 1;
    }
    counts
}

#[inline(always)]
fn count_frequencies_ref<T: Eq + Ord>(vec: &[T]) -> BTreeMap<&T, usize> {
    let mut counts = BTreeMap::new();
    for item in vec {
        *counts.entry(item).or_insert(0) += 1;
    }
    counts
}

#[inline(always)]
fn multiset_intersection<T: Eq + Ord + Clone>(vec1: Vec<T>, vec2: Vec<T>) -> Vec<T> {
    if vec1.is_empty() || vec2.is_empty() {
        return vec![];
    }
    let mut intersection_vec = Vec::with_capacity(vec1.len().min(vec2.len()));
    let mut counts1 = count_frequencies(vec1);
    let mut counts2 = count_frequencies(vec2);
    if counts2.len() < counts1.len() {
        swap(&mut counts1, &mut counts2);
    }
    for (item, count1) in counts1.into_iter() {
        if let Some(&count2) = counts2.get(&item) {
            let min_count = count1.min(count2);
            intersection_vec.extend(repeat_n(item, min_count));
        }
    }
    intersection_vec
}

#[inline(always)]
fn multiset_union<T: Eq + Ord + Clone>(vec1: Vec<T>, vec2: Vec<T>) -> Vec<T> {
    if vec1.is_empty() {
        return vec2;
    }
    if vec2.is_empty() {
        return vec1;
    }
    let counts1 = count_frequencies(vec1);
    let mut counts2 = count_frequencies(vec2);
    for (item, count1) in counts1.into_iter() {
        let union_count = counts2.entry(item).or_insert(0);
        *union_count = (*union_count).max(count1);
    }
    counts2
        .into_iter()
        .flat_map(|(item, count)| repeat_n(item, count))
        .collect()
}

#[inline(always)]
fn multiset_difference<T: Eq + Ord + Clone>(vec1: Vec<T>, vec2: &[T]) -> Vec<T> {
    if vec2.is_empty() {
        return vec1;
    }
    if vec1.is_empty() {
        return vec![];
    }
    let mut difference_vec = Vec::with_capacity(vec1.len());
    let counts1 = count_frequencies(vec1);
    let counts2 = count_frequencies_ref(vec2);

    for (item, mut count) in counts1 {
        if let Some(&count2) = counts2.get(&item) {
            count = count.saturating_sub(count2);
        }
        difference_vec.extend(repeat_n(item, count));
    }
    difference_vec
}

#[inline]
fn fibonacci_factors(term: u128, subset_recursion: bool) -> Vec<Factor> {
    debug!("fibonacci_factors: term {term}, subset_recursion {subset_recursion}");
    if term < SMALL_FIBONACCI_FACTORS.len() as u128 {
        SMALL_FIBONACCI_FACTORS[term as usize]
            .iter()
            .copied()
            .map(Factor::from)
            .collect()
    } else if term.is_multiple_of(2) {
        let mut factors = fibonacci_factors(term >> 1, subset_recursion);
        factors.extend(lucas_factors(term >> 1, subset_recursion));
        factors
    } else if !subset_recursion {
        vec![Factor::Fibonacci(Box::new(term.into()))]
    } else {
        let mut factors = Vec::new();
        let factors_of_term = factorize128(term);
        let mut factors_of_term = factors_of_term
            .into_iter()
            .flat_map(|(key, value)| repeat_n(key, value))
            .collect::<Vec<u128>>();
        let full_set_size = factors_of_term.len();
        for subset in power_multiset(&mut factors_of_term).into_iter() {
            if subset.len() < full_set_size && !subset.is_empty() {
                let product: u128 = subset.into_iter().product();
                if product > 2 {
                    factors = multiset_union(fibonacci_factors(product, false), factors);
                }
            }
        }
        factors
    }
}

#[inline]
fn lucas_factors(term: u128, subset_recursion: bool) -> Vec<Factor> {
    debug!("lucas_factors: term {term}, subset_recursion {subset_recursion}");
    if term < SMALL_LUCAS_FACTORS.len() as u128 {
        SMALL_LUCAS_FACTORS[term as usize]
            .iter()
            .copied()
            .map(Factor::from)
            .collect()
    } else if !subset_recursion {
        vec![Factor::Lucas(Box::new(term.into()))]
    } else {
        let mut factors = Vec::new();
        let mut factors_of_term = factorize128(term);
        let power_of_2 = factors_of_term.remove(&2).unwrap_or(0) as u128;
        let mut factors_of_term = factors_of_term
            .into_iter()
            .flat_map(|(key, value)| repeat_n(key, value))
            .collect::<Vec<u128>>();
        let full_set_size = factors_of_term.len();
        for subset in power_multiset(&mut factors_of_term).into_iter() {
            if subset.len() < full_set_size && !subset.is_empty() {
                let product = subset.into_iter().product::<u128>() << power_of_2;
                if product > 2 {
                    factors = multiset_union(lucas_factors(product, false), factors);
                }
            }
        }
        factors
    }
}

#[inline]
fn power_multiset<T: PartialEq + Ord + Copy>(multiset: &mut Vec<T>) -> Vec<Vec<T>> {
    let mut result = Vec::new();
    multiset.sort_unstable(); // Sort to handle duplicates more easily

    #[inline]
    fn generate_subsets<T: PartialEq + Copy>(
        current_subset: &mut Vec<T>,
        remaining_elements: &mut Vec<T>,
        all_subsets: &mut Vec<Vec<T>>,
    ) {
        // Add the current subset to the result
        all_subsets.push(current_subset.clone());

        if remaining_elements.is_empty() {
            return;
        }

        let mut i = 0;
        while i < remaining_elements.len() {
            let element = remaining_elements.remove(i);
            current_subset.push(element);

            generate_subsets(current_subset, remaining_elements, all_subsets);

            // Backtrack: add the element back and remove from current_subset
            current_subset.pop();
            remaining_elements.insert(i, element);

            // Skip duplicate elements to avoid redundant subsets
            while i < remaining_elements.len() && remaining_elements[i] == element {
                i += 1;
            }
        }
    }

    let mut current_subset = Vec::new();
    generate_subsets(&mut current_subset, multiset, &mut result);
    for subset in result.iter_mut() {
        subset.sort_unstable();
    }
    result.sort_unstable();
    result.dedup();
    result
}

/// Modular inverse using extended Euclidean algorithm
#[inline]
fn modinv(a: u128, m: u128) -> Option<u128> {
    let (mut t, mut newt) = (0i128, 1i128);
    let (mut r, mut newr) = (m as i128, a as i128);

    while newr != 0 {
        let quotient = r / newr;
        t -= quotient * newt;
        swap(&mut t, &mut newt);
        r -= quotient * newr;
        swap(&mut r, &mut newr);
    }

    if r > 1 {
        return None; // no inverse
    }

    if t < 0 {
        t += m as i128;
    }

    Some(t as u128)
}

// Maximum number of times a factor will be repeated when raised to a power, to limit memory usage.
const MAX_REPEATS: u128 = 16;

fn factor_power(a: u128, n: u128) -> (u128, u128) {
    if a == 1 {
        return (1, 0);
    }
    // A u128 can't be a 128th or higher power
    for prime in [
        2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89,
        97, 101, 103, 107, 109, 113, 127,
    ] {
        if let Some(root) = a.nth_root_exact(prime as u32) {
            return match n.checked_mul(prime as u128) {
                Some(product) => factor_power(root, product),
                None => (a, n),
            };
        }
    }
    (a, n)
}

impl FactorFinder {
    #[inline(always)]
    pub fn new() -> FactorFinder {
        // Simple expression
        const E: &str = "([^()+\\-*\\/\\^]+|\\([^()]+\\)|\\([^()]*\\([^()]+\\)[^()]*\\)|\\([^()]*\\([^()]*\\([^()]+\\)[^()]*\\)[^()]*\\))";
        const E_ALLOW_POW: &str = "([^()+\\-*\\/]+|\\([^()]+\\)|\\([^()]*\\([^()]+\\)[^()]*\\)|\\([^()]*\\([^()]*\\([^()]+\\)[^()]*\\)[^()]*\\))";
        const E_ALLOW_ALL: &str = "([^()]+|\\([^()]+\\)|\\([^()]*\\([^()]+\\)[^()]*\\)|\\([^()]*\\([^()]*\\([^()]+\\)[^()]*\\)[^()]*\\))";

        let regexes_as_set = RegexSet::new([
            "^lucas\\((.*)\\)$",
            "^(.*)!$",
            "^(.*)#$",
            "^I(.*)$",
            formatcp!("^{E}\\^{E}(?:\\*{E})?(?:([+-]){E})?$"),
            formatcp!("^{E}\\^{E_ALLOW_POW}([+-]){E}\\^{E_ALLOW_POW}$"),
            "^([0-9]+)$",
            "^([0-9]+\\.\\.+[0-9]+)$",
            formatcp!("^\\({E_ALLOW_ALL}\\)$"),
            formatcp!("^{E}\\^{E_ALLOW_POW}$"),
            "^(.*)/([^()/+-]+|\\([^()]+\\))$",
            "^(.*)\\*([^()\\*+-]+|\\([^()]+\\))$",
            formatcp!("^{E_ALLOW_ALL}([-+])(.*)$"),
        ])
        .unwrap();
        let regexes = regexes_as_set
            .patterns()
            .iter()
            .map(|pat| Regex::new(pat).unwrap())
            .collect();
        let sieve = NaiveBuffer::new();
        FactorFinder {
            regexes,
            regexes_as_set,
            sieve,
        }
    }

    pub fn to_like_powers(&self, left: &Factor, right: &Factor, subtract: bool) -> Vec<Factor> {
        let mut possible_factors = BTreeMap::new();
        let mut new_left = self.simplify(left.clone());
        let mut new_right = self.simplify(right.clone());
        for term in [&mut new_left, &mut new_right] {
            let exponent_u128 = match term {
                Factor::Power { exponent, .. } => self.evaluate_as_u128(exponent),
                Factor::Numeric(a) => {
                    let (a, n) = factor_power(*a, 1);
                    if n > 1 {
                        *term = Factor::Power {
                            base: Numeric(a).into(),
                            exponent: Numeric(n).into(),
                        };
                        Some(n)
                    } else {
                        None
                    }
                }
                _ => None,
            };
            if let Some(exponent_u128) = exponent_u128 {
                factorize128(exponent_u128)
                    .into_iter()
                    .for_each(|(factor, factor_exponent)| {
                        possible_factors.insert(
                            factor,
                            factor_exponent
                                .max(possible_factors.get(&factor).copied().unwrap_or(0)),
                        );
                    })
            }
        }
        if !subtract {
            possible_factors.remove(&2);
        };
        if possible_factors.is_empty() {
            return vec![];
        }
        let mut possible_factors: Vec<_> = possible_factors
            .into_iter()
            .flat_map(|(factor, factor_exponent)| repeat_n(factor, factor_exponent))
            .collect();
        let factor_subsets = power_multiset(&mut possible_factors);
        let mut results = Vec::with_capacity((factor_subsets.len() - 1) * 2);
        for factors in factor_subsets {
            if factors.is_empty() {
                continue;
            }
            let Some(Some(product)) = factors.into_iter().try_reduce(u128::checked_mul) else {
                continue;
            };
            if let Some(left_root) = self.nth_root_exact(&new_left, product)
                && let Some(right_root) = self.nth_root_exact(&new_right, product)
            {
                if subtract && product.is_multiple_of(2) {
                    results.push(self.simplify(Factor::AddSub {
                        left: left_root.clone().into(),
                        right: right_root.clone().into(),
                        subtract: false,
                    }));
                }
                results.push(self.simplify(Factor::AddSub {
                    left: left_root.into(),
                    right: right_root.into(),
                    subtract,
                }));
            }
        }
        results
    }

    pub fn div_exact(&self, mut product: Factor, divisor: Factor) -> Result<Factor, Factor> {
        if product == divisor {
            return Ok(Numeric(1));
        }
        if let Some(product_u128) = self.evaluate_as_u128(&product)
            && let Some(divisor_u128) = self.evaluate_as_u128(&divisor)
        {
            return product_u128
                .div_exact(divisor_u128)
                .map(Numeric)
                .ok_or(Numeric(product_u128));
        }
        match product {
            Factor::Power {
                base,
                ref mut exponent,
            } => {
                if *base == divisor {
                    return Ok(self.simplify(Factor::Power {
                        base,
                        exponent: self
                            .simplify(AddSub {
                                left: take(exponent),
                                right: Numeric(1).into(),
                                subtract: true,
                            })
                            .into(),
                    }));
                } else if let Some(exponent) = self.evaluate_as_u128(exponent)
                    && let Some(divisor_root) = self.nth_root_exact(&divisor, exponent)
                    && let Ok(divided_base) = self.div_exact(*base.clone(), divisor_root)
                {
                    return Ok(self.simplify(Factor::Power {
                        base: divided_base.into(),
                        exponent: Box::new(exponent.into()),
                    }));
                }
                return Err(Factor::Power {
                    base,
                    exponent: take(exponent),
                });
            }
            Factor::Multiply { ref mut terms } => {
                let mut divisor_u128 = self.evaluate_as_u128(&divisor);
                for (index, term) in terms.iter_mut().enumerate() {
                    if *term == divisor {
                        terms.remove(index);
                        return Ok(self.simplify(Factor::Multiply {
                            terms: std::mem::take(terms),
                        }));
                    }
                    if let Some(divisor) = &mut divisor_u128
                        && let Some(term_u128) = self.evaluate_as_u128(term)
                    {
                        let gcd = term_u128.gcd(divisor);
                        if gcd > 1 {
                            *term = (term_u128 / gcd).into();
                            *divisor /= gcd;
                            if *divisor == 1 {
                                return Ok(self.simplify(Factor::Multiply {
                                    terms: std::mem::take(terms),
                                }));
                            }
                        }
                    }
                }
            }
            Factor::Divide {
                ref left,
                ref mut right,
            } => {
                let right = std::mem::take(right);
                return match self.div_exact(*left.clone(), divisor) {
                    Ok(new_left) => Ok(self.simplify(Factor::Divide {
                        left: new_left.into(),
                        right,
                    })),
                    Err(left) => Err(Factor::Divide {
                        left: left.into(),
                        right,
                    }),
                };
            }
            Factor::Factorial(ref term) => {
                if let Some(divisor) = self.evaluate_as_u128(&divisor)
                    && let Some(term) = self.evaluate_as_u128(term)
                {
                    let mut new_term = term;
                    while let Some(divisor) = divisor.div_exact(new_term) {
                        new_term -= 1;
                        if divisor == 1 {
                            return Ok(self.simplify(Factor::Factorial(Numeric(new_term).into())));
                        }
                    }
                }
            }
            Factor::Primorial(ref term) => {
                if let Some(mut divisor) = self.evaluate_as_u128(&divisor)
                    && let Some(term) = self.evaluate_as_u128(term)
                {
                    let mut new_term = term;
                    while self.sieve.is_prime(&new_term, None) == No
                        || divisor
                            .div_exact(new_term)
                            .inspect(|new_divisor| divisor = *new_divisor)
                            .is_some()
                    {
                        new_term -= 1;
                        if divisor == 1 {
                            return Ok(self.simplify(Factor::Primorial(Numeric(new_term).into())));
                        }
                    }
                }
            }
            Factor::BigNumber(ref n) => {
                let mut n_reduced = n.as_str();
                let mut reduced = false;
                let d_reduced = match divisor {
                    Numeric(mut d) => {
                        while d.is_multiple_of(10) && n_reduced.ends_with('0') {
                            reduced = true;
                            n_reduced = &n_reduced[0..(n_reduced.len() - 1)];
                            d /= 10;
                        }
                        Some(Numeric(d))
                    }
                    Factor::BigNumber(d) => {
                        let mut d_reduced = d.as_str();
                        while d_reduced.ends_with('0') && n_reduced.ends_with('0') {
                            reduced = true;
                            d_reduced = &d_reduced[0..(d_reduced.len() - 1)];
                            n_reduced = &n_reduced[0..(n_reduced.len() - 1)];
                        }
                        Some(d.into())
                    }
                    _ => None,
                };
                if reduced && let Some(d_reduced) = d_reduced {
                    return self.div_exact(n_reduced.into(), d_reduced);
                }
            }
            AddSub {
                left,
                right,
                subtract,
            } => {
                return match self.div_exact(*left.clone(), divisor.clone()) {
                    Ok(new_left) => match self.div_exact(*right, divisor) {
                        Ok(new_right) => Ok(self.simplify(Factor::AddSub {
                            left: new_left.into(),
                            right: new_right.into(),
                            subtract,
                        })),
                        Err(right) => Err(AddSub {
                            left,
                            right: right.into(),
                            subtract,
                        }),
                    },
                    Err(left) => Err(AddSub {
                        left: left.into(),
                        right,
                        subtract,
                    }),
                };
            }
            _ => {}
        }
        Err(product)
    }

    pub fn nth_root_exact(&self, factor: &Factor, root: u128) -> Option<Factor> {
        if root == 1 {
            return Some(factor.clone());
        }
        if let Some(factor_u128) = self.evaluate_as_u128(factor) {
            if factor_u128 == 1 {
                return Some(1.into());
            }
            return Some(factor_u128.nth_root_exact(root.try_into().ok()?)?.into());
        }
        match factor {
            Factor::Power { base, exponent } => {
                return Some(Factor::Power {
                    base: base.clone(),
                    exponent: match self.evaluate_as_u128(exponent) {
                        Some(exponent_u128) => exponent_u128.div_exact(root)?.into(),
                        None => self.div_exact(*exponent.clone(), Numeric(root)).ok()?,
                    }
                    .into(),
                });
            }
            Factor::Multiply { terms } => {
                let new_terms = terms
                    .iter()
                    .map(|term| self.nth_root_exact(term, root))
                    .collect::<Option<Vec<_>>>()?;
                return Some(Factor::Multiply { terms: new_terms });
            }
            Factor::Divide { left, right } => {
                let new_left = self.nth_root_exact(left, root)?;
                let new_right = right
                    .iter()
                    .map(|term| self.nth_root_exact(term, root))
                    .collect::<Option<Vec<_>>>()?;
                return Some(Factor::Divide {
                    left: new_left.into(),
                    right: new_right,
                });
            }
            _ => {}
        }
        None
    }

    #[inline(always)]
    pub(crate) fn find_factors_of_u128(input: u128) -> Vec<Factor> {
        debug_assert_ne!(input, 0);
        factorize128(input)
            .into_iter()
            .flat_map(|(factor, power)| repeat_n(Numeric(factor), power))
            .collect()
    }

    #[inline(always)]
    fn estimate_log10_internal(&self, expr: &Factor) -> (u128, u128) {
        debug!("estimate_log10_internal: {expr}");
        match expr {
            Numeric(n) => {
                if *n == 0 {
                    warn!("log10 estimate for 0 was requested");
                    (0, 0)
                } else if *n == 1 {
                    (0, 0)
                } else {
                    (n.ilog10() as u128, (n - 1).ilog10() as u128 + 1)
                }
            }
            Factor::BigNumber(expr) => {
                let len = expr.len();
                ((len - 1) as u128, len as u128)
            }
            Factor::Fibonacci(x) | Factor::Lucas(x) => {
                // Fibonacci or Lucas number
                let Some(term_number) = self.evaluate_as_u128(x) else {
                    warn!("Could not parse term number of a Lucas number: {}", x);
                    return (0, u128::MAX);
                };
                let est_log = term_number as f64 * 0.20898;
                (est_log.floor() as u128, est_log.ceil() as u128 + 1)
            }
            /* TODO: a^n*b+c
                            let (Some(a), Some(n), Some(b), Some(c)) = (
                                self.evaluate_as_u128(&captures[1].into()),
                            self.evaluate_as_u128(&captures[2].into()),
                                match captures.get(3) {
                                    Some(b) => self.evaluate_as_u128(&b.as_str().into()),
                                    None => Some(1),
                                },
                                match captures.get(5) {
                                    Some(c) => self.evaluate_as_u128(&c.as_str().into()),
                                    None => Some(0),
                                },
                            ) else {
                                warn!("Could not parse a^n*b+c expression: {expr}",);
                                return (0, u128::MAX);
                            };
                            let log_anb_lower_bound = (a as f64)
                                .log10()
                                .next_down()
                                .mul_add((n as f64).next_down(), (b as f64).log10().next_down());
                            let log_anb_upper_bound = (a as f64)
                                .log10()
                                .next_up()
                                .mul_add((n as f64).next_up(), (b as f64).log10().next_up());
                            if c == 0 {
                                return (
                                    log_anb_lower_bound.floor() as u128,
                                    log_anb_upper_bound.ceil() as u128,
                                );
                            }
                            let log_abs_c_upper_bound = (c as f64).abs().log10().next_up();
                            Self::addsub_log10(
                                &captures[4][0..=0],
                                log_anb_lower_bound,
                                log_anb_upper_bound,
                                0.0,
                                log_abs_c_upper_bound,
                            )
                        }
             */
            /* TODO: a^x +/- b^y
                            let (Some(a), Some(x), sign, Some(b), Some(y)) = (
                                self.evaluate_as_u128(&captures[1].into()),
                                self.evaluate_as_u128(&captures[2].into()),
                                &captures[3],
                                self.evaluate_as_u128(&captures[4].into()),
                                self.evaluate_as_u128(&captures[5].into()),
                            ) else {
                                return (0, u128::MAX);
                            };
                            let log_ax_lower_bound =
                                (a as f64).log10().next_down() * (x as f64).next_down();
                            let log_ax_upper_bound =
                                (a as f64).log10().next_up() * (x as f64).next_up();
                            let log_by_lower_bound =
                                (b as f64).log10().next_down() * (y as f64).next_down();
                            let log_by_upper_bound =
                                (b as f64).log10().next_up() * (y as f64).next_up();
                            Self::addsub_log10(
                                sign,
                                log_ax_lower_bound,
                                log_ax_upper_bound,
                                log_by_lower_bound,
                                log_by_upper_bound,
                            )
                        }
             */
            Factor::Factorial(input) => {
                // factorial
                let Some(input) = self.evaluate_as_u128(input) else {
                    warn!("Could not parse input to a factorial: {}", input);
                    return (0, u128::MAX);
                };
                let (ln_factorial, _) = ((input + 1) as f64).ln_gamma();

                // LN_10 is already rounded up
                let log_factorial_lower_bound = ln_factorial.next_down() / LN_10;
                let log_factorial_upper_bound = ln_factorial.next_up() / LN_10.next_down();

                (
                    log_factorial_lower_bound.floor() as u128,
                    log_factorial_upper_bound.ceil() as u128,
                )
            }
            Factor::Primorial(input) => {
                // primorial
                let Some(input) = self.evaluate_as_u128(input) else {
                    warn!("Could not parse input to a factorial: {}", input);
                    return (0, u128::MAX);
                };

                // Lower bound is from
                // Rosser, J. Barkley; Schoenfeld, Lowell (1962-03-01).
                // "Approximate formulas for some functions of prime numbers".
                // Illinois Journal of Mathematics 6 (1), p. 70
                // https://projecteuclid.org/journalArticle/Download?urlId=10.1215%2Fijm%2F1255631807
                // (p. 7 of PDF)
                let lower_bound = if input >= 563 {
                    (input as f64 * (1.0 / (2.0 * (input as f64).ln())) / LN_10).ceil() as u128
                } else if input >= 41 {
                    (input as f64 * (1.0 / (input as f64).ln()) / LN_10.next_down()).ceil() as u128
                } else {
                    0
                };
                let upper_bound = (1.01624 / LN_10 * input as f64).floor();
                (lower_bound, upper_bound as u128)
            }
            Factor::ElidedNumber(_) => {
                // Elided numbers from factordb are always at least 51 digits
                (50, u128::MAX)
            }
            Factor::Power { base, exponent } => {
                let Some(exponent) = self.evaluate_as_u128(exponent) else {
                    return (0, u128::MAX);
                };
                if let Some(base) = self.evaluate_as_u128(base) {
                    let lower = (base as f64).log10().next_down() * exponent as f64;
                    let upper = (base as f64).log10().next_up() * (exponent as f64).next_up();
                    (lower.floor() as u128, upper.ceil() as u128)
                } else {
                    let (base_lower, base_upper) = self.estimate_log10_internal(base);
                    (
                        base_lower.saturating_mul(exponent),
                        base_upper.saturating_mul(exponent),
                    )
                }
            }
            Factor::Divide { left, right } => {
                let (num_lower, num_upper) = self.estimate_log10_internal(left);
                let (denom_lower, denom_upper) = right
                    .iter()
                    .map(|term| self.estimate_log10_internal(term))
                    .reduce(|(l1, u1), (l2, u2)| {
                        (
                            l1.saturating_add(l2),
                            u1.saturating_add(u2).saturating_add(1),
                        )
                    })
                    .unwrap();
                let lower = num_lower.saturating_sub(denom_upper.saturating_add(1));
                let upper = num_upper.saturating_sub(denom_lower.saturating_sub(1));
                (lower, upper)
            }
            Factor::Multiply { terms } => {
                // multiplication
                let (product_lower, product_upper) = terms
                    .iter()
                    .map(|term| self.estimate_log10_internal(term))
                    .reduce(|(l1, u1), (l2, u2)| {
                        (
                            l1.saturating_add(l2),
                            u1.saturating_add(u2).saturating_add(1),
                        )
                    })
                    .unwrap();
                (product_lower, product_upper)
            }
            Factor::AddSub {
                left,
                right,
                subtract,
            } => {
                // addition/subtraction
                let (left_lower, left_upper) = self.estimate_log10_internal(left);
                let (right_lower, right_upper) = self.estimate_log10_internal(right);
                Self::addsub_log10(
                    *subtract,
                    left_lower as f64,
                    left_upper as f64,
                    right_lower as f64,
                    right_upper as f64,
                )
            }
            Factor::UnknownExpression(_) => (0, u128::MAX),
        }
    }

    fn addsub_log10(
        subtract: bool,
        left_lower: f64,
        left_upper: f64,
        right_lower: f64,
        right_upper: f64,
    ) -> (u128, u128) {
        let combined_lower = if subtract {
            if right_upper >= left_lower - LOG10_2 {
                0.0
            } else {
                left_lower - LOG10_2
            }
        } else {
            left_lower.max(right_lower)
        };
        let combined_upper = if subtract {
            left_upper
        } else {
            left_upper.max(right_upper) + LOG10_2
        };
        (combined_lower as u128, combined_upper.ceil() as u128)
    }

    pub(crate) fn estimate_log10(&self, expr: &Factor) -> (u128, u128) {
        let (lbound, ubound) = self.estimate_log10_internal(expr);
        if lbound > ubound {
            error!(
                "{expr}: estimate_log10 produced inconsistent bounds: lower bound {lbound}, upper bound {ubound}"
            );
            (0, u128::MAX)
        } else {
            (lbound, ubound)
        }
    }

    pub(crate) fn evaluate_modulo_as_u128(&self, expr: &Factor, modulus: u128) -> Option<u128> {
        if let Some(eval) = self.evaluate_as_u128(expr) {
            return Some(eval % modulus);
        }
        match modulus {
            0 => {
                warn!("Attempted to evaluate {expr} modulo 0");
                return None;
            }
            1 => return Some(0),
            2 | 5 => {
                if let Some(last_digit) = expr.last_digit() {
                    return Some(last_digit as u128 % modulus);
                }
            }
            _ => {}
        }
        match expr {
            Factor::Numeric(n) => Some(n % modulus),
            Factor::BigNumber(_) | Factor::ElidedNumber(_) | Factor::UnknownExpression(_) => None,
            Factor::AddSub {
                left,
                right,
                subtract,
            } => {
                let left = self.evaluate_modulo_as_u128(left, modulus)?;
                let right = self.evaluate_modulo_as_u128(right, modulus)?;
                if *subtract {
                    let diff = left.abs_diff(right);
                    Some(if left > right {
                        diff.rem_euclid(modulus)
                    } else {
                        (modulus - diff.rem_euclid(modulus)) % modulus
                    })
                } else {
                    Some((left + right) % modulus)
                }
            }
            Factor::Multiply { terms } => {
                let mut product = 1;
                for term in terms.iter() {
                    product = (product * self.evaluate_modulo_as_u128(term, modulus)?) % modulus;
                }
                Some(product)
            }
            Factor::Divide { left, right } => {
                let mut result = self.evaluate_modulo_as_u128(left, modulus)?;
                for term in right.iter() {
                    let term_mod = self.evaluate_modulo_as_u128(term, modulus)?;
                    match modinv(term_mod, modulus) {
                        Some(inv) => result = (result * inv) % modulus,
                        None => result = result.div_exact(modulus)?,
                    }
                }
                Some(result)
            }
            Factor::Power { base, exponent } => {
                let base_mod = self.evaluate_modulo_as_u128(base, modulus)?;
                let exp = self.evaluate_as_u128(exponent)?;
                Some(base_mod.powm(exp, &modulus))
            }
            Factor::Fibonacci(term) => {
                let term = self.evaluate_as_u128(term)?;
                Some(Self::pisano(term, vec![0, 1, 1], modulus))
            }
            Factor::Lucas(term) => {
                let term = self.evaluate_as_u128(term)?;
                Some(Self::pisano(term, vec![2, 1], modulus))
            }
            Factor::Factorial(term) => {
                let term = self.evaluate_as_u128(term)?;
                if term >= modulus {
                    return Some(0);
                }
                let mut result = 1;
                for i in 2..=term {
                    result = (result * i) % modulus;
                }
                Some(result)
            }
            Factor::Primorial(term) => {
                let term = self.evaluate_as_u128(term)?;
                if term >= modulus {
                    return Some(0);
                }
                let mut result = 1;
                for i in 2..=term {
                    if self.sieve.is_prime(&i, None) != No {
                        result = (result * i) % modulus;
                    }
                }
                Some(result)
            }
        }
    }

    fn pisano(term: u128, mut sequence: Vec<u128>, modulus: u128) -> u128 {
        let mut zeros = 0; // don't count the initial 0th term for Fibonacci sequence
        loop {
            if sequence.len() as u128 == term + 1 {
                return *sequence.last().unwrap();
            }
            let next_term = (sequence[sequence.len() - 2] + sequence[sequence.len() - 2]) % modulus;
            if next_term == 0 {
                zeros += 1;
            }
            if zeros == 4 && next_term == sequence[0] {
                return sequence[(term % (sequence.len() as u128)) as usize];
            }
            sequence.push(next_term);
        }
    }

    pub(crate) fn simplify(&self, expr: Factor) -> Factor {
        if let Some(expr_u128) = self.evaluate_as_u128(&expr) {
            return Numeric(expr_u128);
        }
        match expr {
            Factor::Multiply { terms } => {
                let new_terms: Vec<Factor> = terms
                    .into_iter()
                    .filter(|term| *term != Numeric(1))
                    .map(|term| self.simplify(term))
                    .collect();
                match new_terms.len() {
                    0 => Factor::Numeric(1),
                    1 => new_terms.into_iter().next().unwrap(),
                    _ => Factor::Multiply {
                        terms: new_terms.into_iter().collect(),
                    },
                }
            }
            Factor::Divide { left, right } => {
                let new_left = self.simplify(*left);
                let mut new_right: Vec<Factor> = right
                    .into_iter()
                    .map(|term| self.simplify(term))
                    .filter(|term| *term != Numeric(1))
                    .collect();
                if let Some((index, _)) = new_right
                    .iter()
                    .enumerate()
                    .find(|(_, term)| **term == new_left)
                {
                    new_right.remove(index);
                }
                if new_right.is_empty() {
                    new_left
                } else {
                    Factor::Divide {
                        left: new_left.into(),
                        right: new_right.into_iter().collect(),
                    }
                }
            }
            Factor::Power { base, exponent } => {
                let mut new_base = self.simplify(*base);
                let mut new_exponent = self.simplify(*exponent);
                if let Some(new_base_u128) = self.evaluate_as_u128(&new_base) {
                    if new_base_u128 == 1 {
                        return Numeric(1);
                    }
                    if let Some(new_exponent_u128) = self.evaluate_as_u128(&new_exponent) {
                        let (factored_base_u128, factored_exponent_u128) =
                            factor_power(new_base_u128, new_exponent_u128);
                        if factored_exponent_u128 != new_exponent_u128 {
                            new_base = Numeric(factored_base_u128);
                            new_exponent = Numeric(factored_exponent_u128);
                        }
                    }
                }
                match new_exponent {
                    Numeric(0) => Numeric(1),
                    Numeric(1) => new_base,
                    _ => Factor::Power {
                        base: new_base.into(),
                        exponent: new_exponent.into(),
                    },
                }
            }
            Factor::Factorial(ref term) | Factor::Primorial(ref term) => match **term {
                Numeric(0) | Numeric(1) => Numeric(1),
                _ => expr,
            },
            Factor::AddSub {
                left,
                right,
                subtract,
            } => Factor::AddSub {
                left: self.simplify(*left).into(),
                right: self.simplify(*right).into(),
                subtract,
            },
            _ => expr,
        }
    }

    pub(crate) fn evaluate_as_u128(&self, expr: &Factor) -> Option<u128> {
        match expr {
            Numeric(n) => Some(*n),
            Factor::BigNumber(_) => None,
            Factor::Lucas(term) => {
                let term = self.evaluate_as_u128(term)?;
                match term {
                    0 => Some(2),
                    1 => Some(1),
                    185.. => None,
                    n => {
                        let mut a = 2u128;
                        let mut b = 1u128;
                        let mut result = 0u128;

                        for _ in 2..=n {
                            result = a + b;
                            a = b;
                            b = result;
                        }
                        Some(result)
                    }
                }
            }
            Factor::Fibonacci(term) => {
                let term = self.evaluate_as_u128(term)?;
                match term {
                    0 => Some(0),
                    1 | 2 => Some(1),
                    186.. => None,
                    n => {
                        let mut a = 1u128;
                        let mut b = 1u128;
                        let mut result = 0u128;
                        for _ in 3..=n {
                            result = a + b;
                            a = b;
                            b = result;
                        }
                        Some(result)
                    }
                }
            }
            /*
                   ANBC_INDEX => {
                       let a = self.evaluate_as_u128(&captures[1].into())?;
                       let n = u32::try_from(self.evaluate_as_u128(&captures[2].into())?).ok()?;
                       let b = if let Some(b) = captures.get(3) {
                           self.evaluate_as_u128(&b.as_str().into())?
                       } else {
                           1
                       };
                       let abs_c = if let Some(c) = captures.get(5) {
                           self.evaluate_as_u128(&c.as_str().into())?
                       } else {
                           0
                       };
                       let anb = a.checked_pow(n)?.checked_mul(b)?;
                       if captures.get(4).is_some_and(|c| c.as_str().starts_with('-')) {
                           anb.checked_sub(abs_c)
                       } else {
                           anb.checked_add(abs_c)
                       }
                   }
                   AXBY_INDEX => {
                       let a = self.evaluate_as_u128(&captures[1].into())?;
                       let x = u32::try_from(self.evaluate_as_u128(&captures[2].into())?).ok()?;
                       let sign = &captures[3];
                       let b = self.evaluate_as_u128(&captures[4].into())?;
                       let y = u32::try_from(self.evaluate_as_u128(&captures[5].into())?).ok()?;
                       let ax = a.checked_pow(x)?;
                       let by = b.checked_pow(y)?;
                       if sign.starts_with('-') {
                           ax.checked_sub(by)
                       } else {
                           ax.checked_add(by)
                       }
                   }
            */
            Factor::Factorial(term) => {
                let term = self.evaluate_as_u128(term)?;
                match term {
                    0 | 1 => Some(1),
                    35.. => None,
                    x => {
                        let mut result = 1;
                        for i in 2..=x {
                            result *= i;
                        }
                        Some(result)
                    }
                }
            }
            Factor::Primorial(term) => {
                let term = self.evaluate_as_u128(term)?;
                match term {
                    0 | 1 => Some(1),
                    103.. => None,
                    x => Some(
                        SMALL_PRIMES
                            .iter()
                            .copied()
                            .map(u128::from)
                            .take_while(|p| *p <= x)
                            .product(),
                    ),
                }
            }
            Factor::ElidedNumber(_) => None,
            Factor::Power { base, exponent } => match self.evaluate_as_u128(base)? {
                0 => Some(0),
                1 => Some(1),
                base => base.checked_pow(u32::try_from(self.evaluate_as_u128(exponent)?).ok()?),
            },
            Factor::Divide { left, right } => {
                let mut result = self.evaluate_as_u128(left)?;
                for term in right.iter() {
                    result = result.checked_div_exact(self.evaluate_as_u128(term)?)?;
                }
                Some(result)
            }
            Factor::Multiply { terms } => {
                let mut result = 1u128;
                for term in terms.iter() {
                    result = result.checked_mul(self.evaluate_as_u128(term)?)?;
                }
                Some(result)
            }
            Factor::AddSub {
                left,
                right,
                subtract,
            } => {
                let left = self.evaluate_as_u128(left)?;
                let right = self.evaluate_as_u128(right)?;
                if *subtract {
                    left.checked_sub(right)
                } else {
                    left.checked_add(right)
                }
            }
            Factor::UnknownExpression(_) => None,
        }
    }

    #[inline(always)]
    fn find_factors(&self, expr: Factor) -> Vec<Factor> {
        info!("find_factors: {expr}");
        if let Some(n) = self.evaluate_as_u128(&expr) {
            return Self::find_factors_of_u128(n);
        }
        match expr {
            Numeric(n) => Self::find_factors_of_u128(n),
            Factor::BigNumber(expr) => Self::factor_big_num(expr),
            Factor::Lucas(ref term) => {
                // Lucas number
                let Some(term_number) = self.evaluate_as_u128(term) else {
                    warn!("Could not parse term number of a Lucas number: {}", term);
                    return vec![expr];
                };
                lucas_factors(term_number, true)
            }
            Factor::Fibonacci(ref term) => {
                // Fibonacci number
                let Some(term_number) = self.evaluate_as_u128(term) else {
                    warn!(
                        "Could not parse term number of a Fibonacci number: {}",
                        term
                    );
                    return vec![expr];
                };
                fibonacci_factors(term_number, true)
            }
            /*
            ANBC_INDEX => {
                // a^n*b + c
                let mut factors = Vec::new();
                let a = Factor::from(&captures[1]);
                let mut b = Numeric(1u128);
                if let Some(b_match) = captures.get(3) {
                    b = Factor::from(b_match.as_str());
                }
                let c_raw_abs: Factor = if let Some(c_match) = captures.get(5) {
                    c_match.as_str().into()
                } else {
                    let n = self.evaluate_as_u128(&captures[2].into())
                        .unwrap_or(MAX_REPEATS)
                        .min(MAX_REPEATS)
                        as usize;
                    factors.extend(repeat_n(self.find_factors(a), n).flatten());
                    factors.extend(self.find_factors(b));
                    return factors;
                };
                let c_neg = match &captures[4] {
                    "-" => true,
                    "+" => false,
                    _ => unsafe { unreachable_unchecked() },
                };
                let gcd_bc =
                    self.find_common_factors(b.clone(), c_raw_abs.clone(), false);
                let b_factors = self.find_factors(b);
                let gcd_ac =
                    self.find_common_factors(a.clone(), c_raw_abs.clone(), false);
                let abs_c = self.find_factors(c_raw_abs);
                let n = Factor::from(&captures[2]);
                drop(captures);
                if let Some(a) = self.evaluate_as_u128(&a)
                    && let Some(n) = self.evaluate_as_u128(&n)
                {
                    let (a, n) = factor_power(a, n);
                    let b_reduced: Vec<Factor> =
                        multiset_difference(b_factors, &gcd_bc);
                    let c_reduced: Vec<Factor> = multiset_difference(abs_c, &gcd_bc);
                    factors.extend(multiset_union(gcd_ac, gcd_bc));
                    if let Some(b) = checked_product_u128(b_reduced.as_slice())
                        && let Some(abs_c_u128) =
                            checked_product_u128(c_reduced.as_slice())
                    {
                        if !a.is_multiple_of(2)
                            && !b.is_multiple_of(2)
                            && !abs_c_u128.is_multiple_of(2)
                        {
                            factors.push(Numeric(2));
                        }
                        let anb_u128 = n
                            .try_into()
                            .ok()
                            .and_then(|n| a.checked_pow(n))
                            .and_then(|an| an.checked_mul(b));
                        let (c, anbc_u128) = if c_neg {
                            (
                                0i128.checked_sub_unsigned(abs_c_u128),
                                anb_u128.and_then(|anb| anb.checked_sub(abs_c_u128)),
                            )
                        } else {
                            (
                                0i128.checked_add_unsigned(abs_c_u128),
                                anb_u128.and_then(|anb| anb.checked_add(abs_c_u128)),
                            )
                        };
                        if let Some(anbc) = anbc_u128 {
                            if factors.is_empty() {
                                info!("Evaluated {expr} as {anbc}");
                            } else {
                                info!(
                                    "Evaluated {expr} as {}*{anbc}",
                                    factors.iter().join("*"),
                                );
                            }
                            factors.extend(Self::find_factors_of_u128(anbc));
                            return factors;
                        }
                        let Some(c) = c else {
                            return factors;
                        };
                        let mut factors_of_n = factorize128(n);
                        let power_of_2 = if c > 0 {
                            factors_of_n.remove(&2).unwrap_or(0) as u32
                        } else {
                            0
                        };
                        let mut odd_factors_of_n = factors_of_n
                            .into_iter()
                            .flat_map(|(key, value)| repeat_n(key, value))
                            .collect::<Vec<u128>>();
                        let odd_factors_of_n_count = odd_factors_of_n.len();
                        let expr = Factor::Expression(expr.clone());
                        for factor_subset in power_multiset(&mut odd_factors_of_n) {
                            if factor_subset.len() == odd_factors_of_n_count {
                                continue;
                            }
                            let subset_product =
                                factor_subset.into_iter().product::<u128>()
                                    << power_of_2;
                            if let Some(modulus) = a
                                .powm(n, &subset_product)
                                .mulm(b, &subset_product)
                                .checked_add(mod_euclid(c, subset_product))
                                && modulus.is_multiple_of(subset_product)
                            {
                                factors
                                    .extend(Self::find_factors_of_u128(subset_product));
                            }
                            if let Ok(prime_for_root) = (n / subset_product).try_into()
                                && (c < 0 || !(n / subset_product).is_multiple_of(2))
                                && let Some(root_c) =
                                    abs_c_u128.nth_root_exact(prime_for_root)
                                && let Some(root_b) = b.nth_root_exact(prime_for_root)
                            {
                                let even_ratio = (n / subset_product).is_multiple_of(2);
                                let (anb_plus_c, anb_minus_c) =
                                    if let Ok(subset_product_u32) =
                                        subset_product.try_into()
                                        && let Some(anb) = a
                                            .checked_pow(subset_product_u32)
                                            .and_then(|an| an.checked_mul(root_b))
                                    {
                                        let anb_plus_c = if (c >= 0 && !even_ratio)
                                            || (c <= 0 && even_ratio)
                                        {
                                            Some(
                                                anb.checked_add(root_c)
                                                    .map(Numeric)
                                                    .unwrap_or_else(|| {
                                                        Factor::Expression(
                                                            format!("{anb}+{root_c}")
                                                                .into(),
                                                        )
                                                    }),
                                            )
                                        } else {
                                            None
                                        };
                                        let anb_minus_c = if c < 0 {
                                            Some(
                                                anb.checked_sub(root_c)
                                                    .map(Numeric)
                                                    .unwrap_or_else(|| {
                                                        Factor::Expression(
                                                            format!("{anb}-{root_c}")
                                                                .into(),
                                                        )
                                                    }),
                                            )
                                        } else {
                                            None
                                        };
                                        (anb_plus_c, anb_minus_c)
                                    } else {
                                        let anb = format!(
                                            "{}{}{}",
                                            a,
                                            if subset_product > 1 {
                                                Owned(format!("^{}", subset_product))
                                            } else {
                                                Borrowed("")
                                            },
                                            if root_b > 1 {
                                                Owned(format!("*{}", root_b))
                                            } else {
                                                Borrowed("")
                                            },
                                        );
                                        let anb_plus_c = if (c >= 0 && !even_ratio)
                                            || (c <= 0 && even_ratio)
                                        {
                                            Some(Factor::Expression(
                                                format!("{anb}+{root_c}").into(),
                                            ))
                                        } else {
                                            None
                                        };
                                        let anb_minus_c = if c < 0 {
                                            Some(Factor::Expression(
                                                format!("{anb}-{root_c}").into(),
                                            ))
                                        } else {
                                            None
                                        };
                                        (anb_plus_c, anb_minus_c)
                                    };
                                for factor in anb_plus_c
                                    .into_iter()
                                    .chain(anb_minus_c.into_iter())
                                {
                                    if factor != expr {
                                        factors
                                            .extend(self.find_factors(factor.clone()));
                                        factors.push(factor);
                                    }
                                }
                            }
                        }
                    }
                } else {
                    factors.extend(multiset_union(gcd_ac, gcd_bc));
                }
                factors
            }
            AXBY_INDEX => {
                //a^x +/- b^y
                let (Some(a), Some(x), sign, Some(b), Some(y)) = (
                    self.evaluate_as_u128(&captures[1].into()),
                    self.evaluate_as_u128(&captures[2].into()),
                    &captures[3],
                    self.evaluate_as_u128(&captures[4].into()),
                    self.evaluate_as_u128(&captures[5].into()),
                ) else {
                    return vec![];
                };
                let (a, x) = factor_power(a, x);
                let (b, y) = factor_power(b, y);
                let c_neg = match sign {
                    "-" => true,
                    "+" => false,
                    _ => unsafe { unreachable_unchecked() },
                };
                let gcd = x.gcd(&y);
                if gcd == 1 {
                    let ax_str = if x > 1 {
                        Some(format!("{a}^{x}"))
                    } else {
                        None
                    };
                    let by_str = if y > 1 {
                        Some(format!("{b}^{y}"))
                    } else {
                        None
                    };
                    let ax = if let Some(ax_str) = ax_str {
                        Factor::Expression(ax_str.into())
                    } else {
                        Numeric(a)
                    };
                    let by = if let Some(by_str) = by_str {
                        Factor::Expression(by_str.into())
                    } else {
                        Numeric(b)
                    };
                    return self.find_common_factors(ax, by, true);
                }
                let mut factors = Vec::new();
                if x == y {
                    for p in SMALL_PRIMES {
                        let p = p as u128;
                        // Compute a*b^{-1} mod p
                        let b_inv = modinv(b % p, p);
                        if b_inv.is_none() {
                            continue;
                        }
                        let g = (a % p * b_inv.unwrap()) % p;

                        // Compute g^x mod p
                        let gx = g.powm(x, &p);

                        let add_check = match sign {
                            "+" => gx == p - 1,
                            "-" => gx == 1,
                            _ => unsafe { unreachable_unchecked() },
                        };
                        if add_check {
                            factors.push(Numeric(p));
                        }
                    }
                }
                if let Some(apb) = if sign == "-" {
                    a.checked_sub(b)
                } else {
                    a.checked_add(b)
                } {
                    factors.extend(Self::find_factors_of_u128(apb));
                }
                let mut factors_of_gcd = factorize128(gcd);
                let power_of_2 = if sign == "+" {
                    factors_of_gcd.remove(&2).unwrap_or(0) as u32
                } else {
                    0
                };
                let mut odd_factors_of_gcd = factors_of_gcd
                    .into_iter()
                    .flat_map(|(key, value)| repeat_n(key, value))
                    .collect::<Vec<u128>>();
                let odd_factors_of_n_count = odd_factors_of_gcd.len();
                let x_ratio = x / gcd;
                let y_ratio = y / gcd;
                for factor_subset in power_multiset(&mut odd_factors_of_gcd) {
                    if factor_subset.len() == odd_factors_of_n_count {
                        continue;
                    }
                    let subset_product =
                        factor_subset.into_iter().product::<u128>() << power_of_2;
                    let even_ratio = (gcd / subset_product).is_multiple_of(2);
                    let x = x_ratio * subset_product;
                    let y = y_ratio * subset_product;
                    let (ax_plus_by, ax_minus_by) = if let Ok(x_u32) = x.try_into()
                        && let Ok(y_u32) = y.try_into()
                        && let Some(ax) = a.checked_pow(x_u32)
                        && let Some(by) = b.checked_pow(y_u32)
                    {
                        let ax_plus_by =
                            if (!c_neg && !even_ratio) || (c_neg && even_ratio) {
                                Some(ax.checked_add(by).map(Numeric).unwrap_or_else(
                                    || Factor::Expression(format!("{ax}+{by}").into()),
                                ))
                            } else {
                                None
                            };
                        let ax_minus_by = if c_neg {
                            Some(ax.checked_sub(by).map(Numeric).unwrap_or_else(|| {
                                Factor::Expression(format!("{ax}-{by}").into())
                            }))
                        } else {
                            None
                        };
                        (ax_plus_by, ax_minus_by)
                    } else {
                        let ax_plus_by = if (!c_neg && !even_ratio)
                            || (c_neg && even_ratio)
                        {
                            Some(Factor::Expression(format!("{a}^{x}+{b}^{y}").into()))
                        } else {
                            None
                        };
                        let ax_minus_by = if c_neg {
                            Some(Factor::Expression(format!("{a}^{x}-{b}^{y}").into()))
                        } else {
                            None
                        };
                        (ax_plus_by, ax_minus_by)
                    };
                    let expr = Factor::Expression(expr.clone());
                    for factor in ax_plus_by.into_iter().chain(ax_minus_by.into_iter())
                    {
                        if factor != expr {
                            factors.extend(self.find_factors(factor.clone()));
                            factors.push(factor);
                        }
                    }
                }
                factors
            }

             */
            Factor::Factorial(ref term) => {
                // factorial
                let Some(input) = self.evaluate_as_u128(term) else {
                    warn!("Could not parse input to factorial function: {}", term);
                    return vec![expr];
                };
                let mut factors = Vec::new();
                for i in 2..=input {
                    factors.extend(Self::find_factors_of_u128(i));
                }
                factors
            }
            Factor::Primorial(ref term) => {
                // primorial
                let Some(input) = self.evaluate_as_u128(term) else {
                    warn!("Could not parse input to primorial function: {}", term);
                    return vec![expr];
                };
                let mut factors = Vec::new();
                for i in 2..=input {
                    if self.sieve.is_prime(&i, None) != No {
                        factors.push(Numeric(i));
                    }
                }
                factors
            }
            Factor::ElidedNumber(n) => match n.chars().last() {
                Some('0') => vec![Numeric(2), Numeric(5)],
                Some('5') => vec![Numeric(5)],
                Some('2' | '4' | '6' | '8') => vec![Numeric(2)],
                Some('1' | '3' | '7' | '9') => vec![],
                x => {
                    error!("Invalid last digit: {x:?}");
                    vec![]
                }
            },
            Factor::Power { base, exponent } => {
                let power = self
                    .evaluate_as_u128(&exponent)
                    .unwrap_or(MAX_REPEATS)
                    .min(MAX_REPEATS) as usize;
                let base_factors = self.find_factors(*base.clone());
                repeat_n(base_factors, power).flatten().collect()
            }
            Factor::Divide { left, right } => {
                // division
                let mut factors = self.find_factors(*left.clone());
                for term in right.iter().cloned() {
                    let denom_factors = self.find_factors(term);
                    factors = multiset_difference(factors, &denom_factors);
                    if factors.is_empty() {
                        return vec![];
                    }
                }
                factors
            }
            Factor::Multiply { terms } => {
                // multiplication
                let mut factors = Vec::new();
                for term in terms.iter() {
                    let term_factors = self.find_factors(term.clone());
                    if term_factors.is_empty() {
                        factors.push(term.clone());
                    } else {
                        factors.extend(term_factors);
                    }
                }
                factors
            }
            Factor::AddSub {
                ref left,
                ref right,
                subtract,
            } => {
                let mut common_factors = self.find_common_factors(*left.clone(), *right.clone());
                for prime in SMALL_PRIMES {
                    if self.evaluate_modulo_as_u128(&expr, prime as u128) == Some(0) {
                        common_factors.push(Numeric(prime as u128));
                    }
                }
                common_factors.sort();
                common_factors.dedup();
                let mut factors: Vec<_> = common_factors
                    .iter()
                    .flat_map(|factor| self.div_exact(expr.clone(), factor.clone()).ok())
                    .collect();
                factors.extend(common_factors);
                factors.extend(self.to_like_powers(left, right, subtract));
                factors
            }
            Factor::UnknownExpression(_) => vec![expr],
        }
    }

    fn factor_big_num(expr: HipStr) -> Vec<Factor> {
        let mut factors = Vec::new();
        let mut expr_short = expr.as_str();
        while expr_short != "0"
            && let Some(stripped) = expr_short.strip_suffix('0')
        {
            factors.push(Numeric(2));
            factors.push(Numeric(5));
            expr_short = stripped;
        }
        if let Ok(num) = expr_short.parse::<u128>() {
            factors.extend(Self::find_factors_of_u128(num));
        } else {
            match expr_short.chars().last() {
                Some('5') => factors.push(Numeric(5)),
                Some('2' | '4' | '6' | '8') => factors.push(Numeric(2)),
                Some('1' | '3' | '7' | '9') => {}
                x => {
                    error!("Invalid last digit: {x:?}");
                }
            }
            let sum_of_digits: u128 = expr_short
                .chars()
                .map(|digit| digit as u128 - '0' as u128)
                .sum();
            match sum_of_digits % 9 {
                0 => {
                    factors.extend([Numeric(3), Numeric(3)]);
                }
                3 | 6 => {
                    factors.push(Numeric(3));
                }
                _ => {}
            }
            if expr_short.len() >= 2 {
                factors.push(expr_short.into());
            } else {
                // All other single-digit numbers are handled by the 2, 5, 3 and 9 cases
                match expr_short {
                    "4" => {
                        factors.push(Numeric(2));
                    }
                    "7" => {
                        factors.push(Numeric(7));
                    }
                    "8" => {
                        factors.extend([Numeric(2), Numeric(2)]);
                    }
                    _ => {}
                }
            }
        }
        factors
    }

    #[inline]
    fn find_common_factors(&self, expr1: Factor, expr2: Factor) -> Vec<Factor> {
        if let Some(num1) = self.evaluate_as_u128(&expr1)
            && let Some(num2) = self.evaluate_as_u128(&expr2)
        {
            Self::find_factors_of_u128(num1.gcd(&num2))
        } else {
            let expr1_factors = self.find_factors(expr1);
            if expr1_factors.is_empty() {
                return vec![];
            }
            let expr2_factors = self.find_factors(expr2);
            multiset_intersection(expr1_factors, expr2_factors)
        }
    }

    /// Returns all unique, nontrivial factors we can find.
    #[inline(always)]
    pub fn find_unique_factors(&self, expr: Factor) -> Box<[Factor]> {
        let mut factors = self.find_factors(expr.clone());
        factors.retain(|f| f.as_u128() != Some(1) && f.may_be_proper_divisor_of(&expr));
        factors.sort();
        factors.dedup();
        if factors.is_empty() {
            warn!("No factors found for expression {expr}");
        } else {
            info!(
                "Found factors of expression {expr}: {}",
                factors.iter().join(", ")
            );
        }
        factors.into_boxed_slice()
    }
}

#[derive(Clone, Default, Debug)]
pub struct ProcessedStatusApiResponse {
    pub status: Option<NumberStatus>,
    pub factors: Box<[Factor]>,
    pub id: Option<u128>,
}

#[derive(Eq, PartialEq, Ord, PartialOrd, Copy, Clone, Debug)]
pub enum NumberStatus {
    Unknown,
    UnfactoredComposite,
    PartlyFactoredComposite,
    Prime, // includes PRP
    FullyFactored,
}

pub trait NumberStatusExt {
    fn is_known_fully_factored(&self) -> bool;
}

impl NumberStatusExt for Option<NumberStatus> {
    #[inline]
    fn is_known_fully_factored(&self) -> bool {
        matches!(
            self,
            Some(NumberStatus::FullyFactored) | Some(NumberStatus::Prime)
        )
    }
}

#[cfg(test)]
mod tests {
    use crate::algebraic::Factor::Numeric;
    use crate::algebraic::{
        Factor, FactorFinder, SMALL_FIBONACCI_FACTORS, SMALL_LUCAS_FACTORS, factor_power,
        fibonacci_factors, lucas_factors, modinv, multiset_difference, multiset_intersection,
        multiset_union, power_multiset,
    };
    use itertools::Itertools;
    use std::iter::repeat_n;

    #[test]
    fn test_anbc() {
        let finder = FactorFinder::new();
        let expr = format!("{}^9*3+3", u128::MAX);
        let factors = finder.find_factors(expr.into());
        println!("{}", factors.iter().join(", "));
        assert!(factors.contains(&3.into()));
        assert!(factors.contains(&format!("{}^9+1", u128::MAX).into()));
    }

    #[test]
    fn test_anbc_2() {
        let finder = FactorFinder::new();
        let factors = finder.find_factors("6^200600+1".into());
        println!("{}", factors.iter().join(", "));

        // Should contain 6^8+1
        assert!(factors.contains(&(6u128.pow(8) + 1).into()));

        // Shouldn't contain 6^5+1
        assert!(!factors.contains(&(6u128.pow(5) + 1).into()));
        assert!(!factors.contains(&7.into()));
        assert!(!factors.contains(&11.into()));
        assert!(!factors.contains(&101.into()));
    }

    #[test]
    fn test_anbc_3() {
        let finder = FactorFinder::new();
        let factors = finder.find_factors("6^1337*5-15".into());

        assert!(factors.contains(&3.into())); // common factor of a^x and c
        assert!(factors.contains(&5.into())); // common factor of b and c
    }

    #[test]
    fn test_anb_minus_c() {
        let finder = FactorFinder::new();
        let expr = format!("{}^24-1", u128::MAX);
        let factors = finder.find_factors(expr.into());
        println!("{}", factors.iter().join(", "));
        assert!(factors.contains(&format!("{}^12-1", u128::MAX).into()));
        assert!(factors.contains(&format!("{}^12+1", u128::MAX).into()));
        assert!(factors.contains(&format!("{}^8-1", u128::MAX).into()));
        assert!(!factors.contains(&format!("{}^8+1", u128::MAX).into()));
        assert!(factors.contains(&format!("{}^6+1", u128::MAX).into()));
        assert!(factors.contains(&format!("{}^6-1", u128::MAX).into()));
        assert!(factors.contains(&format!("{}^4+1", u128::MAX).into()));
        assert!(factors.contains(&format!("{}^4-1", u128::MAX).into()));
        assert!(factors.contains(&format!("{}^3+1", u128::MAX).into()));
        assert!(factors.contains(&format!("{}^3-1", u128::MAX).into()));
        assert!(factors.contains(&format!("{}^2+1", u128::MAX).into()));
        assert!(factors.contains(&format!("{}^2-1", u128::MAX).into()));
    }

    #[test]
    fn test_modinv() {
        assert_eq!(modinv(3, 11), Some(4));
        assert_eq!(modinv(17, 3120), Some(2753));
        assert_eq!(modinv(6, 9), None);
    }

    #[test]
    fn test_axby() {
        let finder = FactorFinder::new();
        let factors = finder.find_factors("1297^400-901^400".into());
        println!("{}", factors.iter().sorted().unique().join(","));
        assert!(factors.contains(&Numeric(2)));
        assert!(factors.contains(&Numeric(3)));
        assert!(factors.contains(&Numeric(5)));
        assert!(factors.contains(&Numeric(11)));
        assert!(factors.contains(&"1297^100-901^100".into()));
        assert!(factors.contains(&"1297^80-901^80".into()));
        assert!(factors.contains(&"1297^100+901^100".into()));
        assert!(!factors.contains(&"1297^80+901^80".into()));
        let factors = finder.find_factors("1297^390-901^390".into());
        println!("{}", factors.iter().sorted().unique().join(","));
        assert!(factors.contains(&Numeric(2)));
        assert!(factors.contains(&Numeric(3)));
        assert!(!factors.contains(&Numeric(5)));
        assert!(factors.contains(&Numeric(11)));
        assert!(factors.contains(&"1297^130-901^130".into()));
        assert!(factors.contains(&"1297^195-901^195".into()));
        assert!(!factors.contains(&"1297^130+901^130".into()));
        assert!(factors.contains(&"1297^195+901^195".into()));
        finder.find_factors("1297^1234-901^1".into());
        assert!(factors.contains(&Numeric(2)));
        assert!(factors.contains(&Numeric(3)));

        // These expressions are negative but should not crash
        finder.find_factors("1297^1-901^123".into());
        finder.find_factors("901^1-1297^1".into());
    }

    #[test]
    fn test_chain() {
        let finder = FactorFinder::new();
        let factors = finder.find_factors("2^8+3*5-1".into());
        assert!(factors.contains(&Numeric(2)));
    }

    #[test]
    fn test_chain_2() {
        let finder = FactorFinder::new();
        let factors = finder.find_factors("(2^9+1)^2*7^2/361".into());
        assert!(factors.contains(&Numeric(3)));
        assert!(factors.contains(&Numeric(7)));
        assert!(!factors.contains(&Numeric(19)));
    }

    #[test]
    fn test_mul_chain() {
        let finder = FactorFinder::new();
        let factors = finder.find_factors("2^8*3*5".into());
        assert!(factors.contains(&Numeric(2)));
        assert!(factors.contains(&Numeric(3)));
        assert!(factors.contains(&Numeric(5)));
    }

    #[test]
    fn test_div_chain() {
        let finder = FactorFinder::new();
        let factors = finder.find_factors("210/2/5".into());
        assert!(factors.contains(&Numeric(3)));
        assert!(factors.contains(&Numeric(7)));
        assert!(!factors.contains(&Numeric(2)));
        assert!(!factors.contains(&Numeric(5)));
    }

    #[test]
    fn test_mixed_chain() {
        let finder = FactorFinder::new();
        let expr = format!(
            "(2^256-1)*(3^200+1)*(10^50)*((12^368-1)^2)/20/1{}",
            &repeat_n('0', 50).collect::<String>()
        );
        let factors = finder.find_factors(expr.into());
        println!("{}", factors.iter().join(","));
        assert!(!factors.contains(&Numeric(2)));
        assert!(factors.contains(&Numeric(3)));
        assert!(!factors.contains(&Numeric(5)));
        assert!(factors.contains(&Numeric(11)));
    }

    #[test]
    fn test_addition_chain() {
        let finder = FactorFinder::new();
        let factors = finder.find_factors("7^5432+3*7^4321+7^321+7^21".into());
        println!("{}", factors.iter().join(","));
        assert!(factors.contains(&Numeric(2)));
        assert!(factors.contains(&Numeric(7)));
        let factors = finder.find_factors("7^5432+3*7^4321+7^321+7^21+1".into());
        assert!(!factors.contains(&Numeric(2)));
        assert!(!factors.contains(&Numeric(7)));
        let factors = finder.find_factors("3*7^5432+7^4321+7^321+1".into());
        assert!(factors.contains(&Numeric(2)));
        assert!(!factors.contains(&Numeric(7)));
        let factors = finder.find_factors("7^5432-7^4321-3*7^321-1".into());
        assert!(factors.contains(&Numeric(2)));
        assert!(!factors.contains(&Numeric(7)));
    }

    #[test]
    fn test_power() {
        let finder = FactorFinder::new();
        let factors = finder.find_factors("(2^7-1)^2".into());
        assert_eq!(factors, Vec::<Factor>::from([Numeric(127), Numeric(127)]));
    }

    #[test]
    fn test_power_associativity() {
        let expr = "2^3^4".into();
        let finder = FactorFinder::new();
        assert_eq!(finder.evaluate_as_u128(&expr), Some(1 << 81));
    }

    #[test]
    fn test_division_associativity() {
        let expr = "20/5/2".into();
        let finder = FactorFinder::new();
        assert_eq!(finder.evaluate_as_u128(&expr), Some(2));
    }

    #[test]
    fn test_stack_depth() {
        // unsafe { backtrace_on_stack_overflow::enable() };
        let expr = repeat_n("(2^9+1)", 1 << 16).join("*").into();
        let finder = FactorFinder::new();
        finder.estimate_log10_internal(&expr);
        finder.evaluate_as_u128(&expr);
        finder.find_factors(expr);
    }

    #[test]
    fn test_stack_depth_2() {
        const PRIMORIAL: u128 = 2 * 3 * 5 * 7 * 11 * 13 * 17 * 19;
        lucas_factors(PRIMORIAL, true);
        fibonacci_factors(PRIMORIAL, true);
    }

    #[test]
    fn test_parse() {
        let factors = FactorFinder::new().find_factors("I(17#)".into());
        // lucas_factors(PRIMORIAL, true);
        assert!(factors.contains(&Numeric(13)));
    }

    #[test]
    fn test_nested_parens() {
        let factors = FactorFinder::new().find_factors("12^((2^7-1)^2)-1".into());
        println!("{factors:?}");
        assert!(factors.contains(&Numeric(11)));
    }

    #[test]
    fn test_factor_power() {
        assert_eq!(
            factor_power(5474401089420219382077155933569751763, 16),
            (3, 16 * 77)
        );
        // (3^77)^16+1
        let factors =
            FactorFinder::new().find_factors("5474401089420219382077155933569751763^16+1".into());
        println!("{}", factors.iter().join(","));
        // factors of 3^16+1
        // assert!(factors.contains(&Numeric(2)));
        assert!(factors.contains(&(3u128.pow(16) + 1).into()));
    }

    #[test]
    fn test_lucas() {
        let factors = lucas_factors(5040, true);
        let mut unique_factors = factors.clone();
        unique_factors.sort();
        unique_factors.dedup();
        assert_eq!(factors.len(), unique_factors.len());
        println!("{}", factors.iter().join(", "));
        for odd_divisor in [35, 45, 63, 105, 315] {
            for factor in SMALL_LUCAS_FACTORS[5040 / odd_divisor] {
                assert!(factors.contains(&(*factor).into()));
            }
        }
    }

    #[test]
    fn test_fibonacci() {
        let factors = fibonacci_factors(5040, true);
        let larger_factors = factors
            .iter()
            .cloned()
            .filter(|f| if let Numeric(n) = f { *n > 7 } else { true })
            .collect::<Vec<_>>();
        let mut unique_larger_factors = larger_factors.clone();
        unique_larger_factors.sort();
        unique_larger_factors.dedup();
        assert_eq!(larger_factors.len(), unique_larger_factors.len());
        println!("{}", factors.iter().join(", "));
        for divisor in [
            1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 16, 18, 20, 21, 24, 28, 30, 35, 36, 40, 42,
            45, 48, 56, 60, 63, 70, 72, 80, 84, 90, 105, 112, 120, 126, 140, 144, 168, 180,
        ] {
            for factor in SMALL_FIBONACCI_FACTORS[divisor] {
                assert!(factors.contains(&(*factor).into()));
            }
        }
    }

    #[test]
    fn test_power_multiset() {
        let mut multiset = vec![2, 2, 3, 3, 5];
        let power_multiset = power_multiset(&mut multiset);
        println!("{:?}", power_multiset);
        assert_eq!(power_multiset.len(), 18);
        assert!(power_multiset.contains(&vec![]));
        assert!(power_multiset.contains(&vec![2]));
        assert!(power_multiset.contains(&vec![2, 2]));
        assert!(power_multiset.contains(&vec![3]));
        assert!(power_multiset.contains(&vec![2, 3]));
        assert!(power_multiset.contains(&vec![2, 2, 3]));
        assert!(power_multiset.contains(&vec![3, 3]));
        assert!(power_multiset.contains(&vec![2, 3, 3]));
        assert!(power_multiset.contains(&vec![2, 2, 3, 3]));
        assert!(power_multiset.contains(&vec![5]));
        assert!(power_multiset.contains(&vec![2, 5]));
        assert!(power_multiset.contains(&vec![2, 2, 5]));
        assert!(power_multiset.contains(&vec![3, 5]));
        assert!(power_multiset.contains(&vec![2, 3, 5]));
        assert!(power_multiset.contains(&vec![2, 2, 3, 5]));
        assert!(power_multiset.contains(&vec![3, 3, 5]));
        assert!(power_multiset.contains(&vec![2, 3, 3, 5]));
        assert!(power_multiset.contains(&vec![2, 2, 3, 3, 5]));
    }

    #[test]
    fn test_multiset_union() {
        let multiset_1 = vec![2, 2, 3, 5, 7];
        let multiset_2 = vec![2, 3, 3, 5, 11];
        let mut union = multiset_union(multiset_1, multiset_2);
        union.sort_unstable();
        assert_eq!(union, vec![2, 2, 3, 3, 5, 7, 11]);
    }

    #[test]
    fn test_multiset_intersection() {
        let multiset_1 = vec![2, 2, 3, 3, 5, 7];
        let multiset_2 = vec![2, 3, 3, 5, 11];
        let mut intersection = multiset_intersection(multiset_1, multiset_2);
        intersection.sort_unstable();
        assert_eq!(intersection, vec![2, 3, 3, 5]);
    }

    #[test]
    fn test_multiset_difference() {
        let multiset_1 = vec![2, 2, 3, 3, 5, 7];
        let multiset_2 = vec![2, 3, 3, 3, 5, 11];
        let difference: Vec<i32> = multiset_difference(multiset_1.clone(), &multiset_2);
        assert_eq!(difference, vec![2, 7]);
        assert!(multiset_difference(vec![], &multiset_2).is_empty());
        assert!(multiset_difference(multiset_1.clone(), &multiset_1).is_empty());
    }

    #[test]
    fn test_estimate_log10() {
        let finder = FactorFinder::new();
        let (lower, upper) = finder.estimate_log10_internal(&Numeric(99));
        assert_eq!(lower, 1);
        assert_eq!(upper, 2);
        let (lower, upper) = finder.estimate_log10_internal(&Numeric(100));
        assert_eq!(lower, 2);
        assert_eq!(upper, 2);
        let (lower, upper) = finder.estimate_log10_internal(&Numeric(101));
        assert_eq!(lower, 2);
        assert_eq!(upper, 3);
        let (lower, upper) = finder.estimate_log10_internal(&Factor::BigNumber(
            ("1".to_string() + &repeat_n('0', 50).collect::<String>()).into(),
        ));
        assert_eq!(lower, 50);
        assert!(upper == 50 || upper == 51);
        let (lower, upper) = finder.estimate_log10_internal(&Factor::BigNumber(
            repeat_n('9', 50).collect::<String>().into(),
        ));
        assert_eq!(lower, 49);
        assert!(upper == 49 || upper == 50);
        let (lower, upper) = finder.estimate_log10_internal(&"I1234".into());
        assert_eq!(lower, 257);
        assert!(upper == 258 || upper == 259);
        let (lower, upper) = finder.estimate_log10_internal(&"lucas(1234)".into());
        assert_eq!(lower, 257);
        assert!(upper == 258 || upper == 259);
        let (lower, upper) = finder.estimate_log10_internal(&"2^607-1".into());
        assert!(lower == 182 || lower == 181);
        assert_eq!(upper, 183);
        let (lower, upper) = finder.estimate_log10_internal(&"10^200-1".into());
        assert!(lower == 198 || lower == 199);
        assert!(upper == 200 || upper == 201);
        let (lower, upper) = finder.estimate_log10_internal(&"10^200+1".into());
        assert!(lower == 199 || lower == 200);
        assert!(upper == 201 || upper == 202);
        let (lower, upper) = finder.estimate_log10_internal(&"10^200*31-1".into());
        assert!(lower >= 199);
        assert!(lower <= 201);
        assert!(upper >= 202);
        assert!(lower <= 204);
        let (lower, upper) = finder.estimate_log10_internal(&"100!".into());
        assert_eq!(lower, 157);
        assert_eq!(upper, 158);
        let (lower, upper) = finder.estimate_log10_internal(&"100#".into());
        assert!(lower <= 36);
        assert!(upper >= 37);
        assert!(upper <= 44);
        let (lower, upper) = finder.estimate_log10_internal(&"20+30".into());
        assert_eq!(lower, 1);
        assert!(upper == 2 || upper == 3);
        let (lower, upper) = finder.estimate_log10_internal(&"30-19".into());
        assert!(lower <= 1);
        assert_eq!(upper, 2);
        let (lower, upper) = finder.estimate_log10_internal(&"11*11".into());
        assert_eq!(lower, 2);
        assert!(upper >= 3);
        let (lower, upper) = finder.estimate_log10_internal(&"(2^769-1)/1591805393".into());
        assert!(lower >= 219 && lower <= 222);
        assert!(upper >= 223 && upper <= 225);
        let (lower, upper) = finder.estimate_log10_internal(&"3^5000-4^2001".into());
        assert!(lower == 2385 || lower == 2384);
        assert!(upper == 2386 || upper == 2387);
    }

    #[test]
    fn test_evaluate_as_u128() {
        let finder = FactorFinder::new();
        assert_eq!(
            finder.evaluate_as_u128(&"2^127-1".into()),
            Some(i128::MAX as u128)
        );
        assert_eq!(
            finder.evaluate_as_u128(&"(5^6+1)^2-1".into()),
            Some(244171875)
        );
        assert_eq!(finder.evaluate_as_u128(&"3^3+4^4+5^5".into()), Some(3408));
    }

    #[test]
    fn test_may_be_proper_divisor_of() {
        fn may_be_proper_divisor_of(left: &str, right: &str) -> bool {
            Factor::from(left).may_be_proper_divisor_of(&Factor::from(right))
        }
        /*
        assert!(may_be_proper_divisor_of("123", "369^2"));
        assert!(!may_be_proper_divisor_of("2", "34567"));
        assert!(may_be_proper_divisor_of("2", "345-67"));
        assert!(!may_be_proper_divisor_of("12345", "54321"));
        assert!(!may_be_proper_divisor_of("12345", "12345"));
        assert!(!may_be_proper_divisor_of("54321", "12345"));
        assert!(!may_be_proper_divisor_of("123456789123456789123456789123456789123456789", "123456789123456789123456789123456789123456789/3"));
        */
        assert!(!may_be_proper_divisor_of("2^1234-1", "(2^1234-1)/3"));
    }
}
