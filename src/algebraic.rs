use crate::algebraic::Factor::{AddSub, Multiply, Numeric};
use crate::{MAX_ID_EQUAL_TO_VALUE, write_bignum};
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
use std::cell::RefCell;
use std::cmp::{Ordering, PartialEq};
use std::collections::{BTreeMap, BTreeSet};
use std::f64::consts::LN_10;
use std::fmt::{Display, Formatter};
use std::hash::Hash;
use std::hint::unreachable_unchecked;
use std::iter::repeat_n;
use std::mem::{swap, take};
use std::rc::Rc;

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
pub struct BigNumber(HipStr<'static>);

impl PartialOrd for BigNumber {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for BigNumber {
    fn cmp(&self, other: &Self) -> Ordering {
        self.0
            .len()
            .cmp(&other.0.len())
            .then_with(|| self.0.cmp(&other.0))
    }
}

impl AsRef<str> for BigNumber {
    fn as_ref(&self) -> &str {
        self.0.as_str()
    }
}

impl Display for BigNumber {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        self.0.fmt(f)
    }
}

impl<T: Into<HipStr<'static>>> From<T> for BigNumber {
    fn from(value: T) -> Self {
        BigNumber(value.into())
    }
}

#[derive(Clone, Debug, Hash, Eq, PartialEq, Ord, PartialOrd)]
pub enum Factor {
    Numeric(u128),
    BigNumber(BigNumber),
    ElidedNumber(HipStr<'static>),
    UnknownExpression(HipStr<'static>),
    AddSub {
        left: Rc<Factor>,
        right: Rc<Factor>,
        subtract: bool,
    },
    Multiply {
        terms: Vec<Rc<Factor>>,
    },
    Divide {
        left: Rc<Factor>,
        right: Vec<Rc<Factor>>,
    },
    Power {
        base: Rc<Factor>,
        exponent: Rc<Factor>,
    },
    Fibonacci(Rc<Factor>),
    Lucas(Rc<Factor>),
    Factorial(Rc<Factor>),
    Primorial(Rc<Factor>),
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

    #[cache_left_rec]
    pub rule arithmetic() -> Factor = precedence!{
      x:(@) "+" y:@ { Factor::AddSub { left: x.into(), right: y.into(), subtract: false } }
      x:(@) "-" y:@ { Factor::AddSub { left: x.into(), right: y.into(), subtract: true } }
      --
      x:(@) "/" y:@ { let mut x = x;
        if let Factor::Divide { ref mut right, .. } = x {
            right.push(y.into());
            x
        } else {
            Factor::Divide { left: x.into(), right: vec![y.into()] }
        }
      }
      --
      x:(@) "*" y:@ { let mut x = x;
        if let Factor::Multiply { ref mut terms, .. } = x {
            terms.push(y.into());
            x
        } else {
            Factor::Multiply { terms: vec![x.into(), y.into()] }
        }
      }
      --
      x:@ "^" y:(@) { Factor::Power { base: x.into(), exponent: y.into() } }
      --
      x:@ "!" { Factor::Factorial(x.into()) }
      x:@ y:$("#"+) {
                    let hashes = y.len();
                    let mut output = x;
                    for _ in 0..(hashes >> 1) {
                        output = Factor::Primorial(Numeric(SIEVE.with_borrow_mut(|sieve| sieve.nth_prime(evaluate_as_u128(&output).unwrap() as u64)) as u128).into());
                    }
                    if !hashes.is_multiple_of(2) {
                        output = Factor::Primorial(output.into())
                    };
                    output
                }
      --
      "M" x:@ { Factor::AddSub { left: Factor::Power { base: Numeric(2).into(), exponent: Rc::new(x) }.into(), right: Factor::one(), subtract: true } }
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
  }
}

impl Factor {
    thread_local! {
        static ONE: Rc<Factor> = Rc::new(Numeric(1));
        static TWO: Rc<Factor> = Rc::new(Numeric(2));
        static THREE: Rc<Factor> = Rc::new(Numeric(3));
        static FIVE: Rc<Factor> = Rc::new(Numeric(5));
    }
    pub fn one() -> Rc<Factor> {
        Factor::ONE.with(Rc::clone)
    }
    pub fn two() -> Rc<Factor> {
        Factor::TWO.with(Rc::clone)
    }
    pub fn three() -> Rc<Factor> {
        Factor::THREE.with(Rc::clone)
    }
    pub fn five() -> Rc<Factor> {
        Factor::FIVE.with(Rc::clone)
    }
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
    pub fn to_owned_string(&self) -> HipStr<'static> {
        match self {
            Numeric(n) => n.to_string().into(),
            Factor::BigNumber(s) => s.0.clone(),
            _ => self.to_string().into(),
        }
    }

    #[inline(always)]
    pub fn as_str_non_u128(&self) -> Option<HipStr<'static>> {
        match self {
            Numeric(_) => None,
            Factor::BigNumber(n) => Some(n.0.clone()),
            _ => Some(self.to_string().into()),
        }
    }

    #[inline(always)]
    fn last_digit(&self) -> Option<u8> {
        match self {
            Factor::BigNumber(BigNumber(n)) | Factor::ElidedNumber(n) => {
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

impl From<BigNumber> for Factor {
    #[inline(always)]
    fn from(value: BigNumber) -> Self {
        Factor::BigNumber(value)
    }
}

macro_rules! factor_from_str {
    ($type:ty) => {
        impl From<$type> for Factor {
            #[inline(always)]
            fn from(value: $type) -> Self {
                expression_parser::arithmetic(value.as_str())
                    .map(|factor| Rc::unwrap_or_clone(simplify(factor.into())))
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
            Factor::BigNumber(s) => write_bignum(f, s.as_ref()),
            Factor::UnknownExpression(e) => e.fmt(f),
            Factor::ElidedNumber(e) => e.fmt(f),
            AddSub {
                left,
                right,
                subtract,
            } => f.write_fmt(format_args!(
                "({left}){}({right})",
                if *subtract { '-' } else { '+' }
            )),
            Multiply { terms } => f.write_fmt(format_args!("({})", terms.iter().join(")*("))),
            Factor::Divide { left, right } => {
                f.write_fmt(format_args!("({left})/({})", right.iter().join(")/(")))
            }
            Factor::Power { base, exponent } => f.write_fmt(format_args!("({base})^({exponent})")),
            Factor::Factorial(input) => f.write_fmt(format_args!("({input}!)")),
            Factor::Primorial(input) => f.write_fmt(format_args!("({input}#)")),
            Factor::Fibonacci(input) => f.write_fmt(format_args!("I({input})")),
            Factor::Lucas(input) => f.write_fmt(format_args!("lucas({input})")),
        }
    }
}

thread_local! {
    static SIEVE: RefCell<NaiveBuffer> = RefCell::new(NaiveBuffer::new());
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
fn multiset_union<T: Eq + Ord + Clone>(mut vecs: Vec<Vec<T>>) -> Vec<T> {
    vecs.retain(|vec| !vec.is_empty());
    match vecs.len() {
        0 => return vec![],
        1 => return vecs.pop().unwrap(),
        _ => {}
    }
    let mut total_counts = BTreeMap::new();
    for vec in vecs {
        let counts = count_frequencies(vec);
        for (item, count) in counts {
            let total = total_counts.entry(item).or_insert(count);
            *total = (*total).max(count);
        }
    }
    total_counts
        .into_iter()
        .flat_map(|(item, count)| repeat_n(item, count))
        .collect()
}

#[inline]
fn fibonacci_factors(term: u128, subset_recursion: bool) -> Vec<Rc<Factor>> {
    debug!("fibonacci_factors: term {term}, subset_recursion {subset_recursion}");
    if term < SMALL_FIBONACCI_FACTORS.len() as u128 {
        SMALL_FIBONACCI_FACTORS[term as usize]
            .iter()
            .copied()
            .map(|x| Factor::Numeric(x).into())
            .collect()
    } else if term.is_multiple_of(2) {
        let mut factors = fibonacci_factors(term >> 1, subset_recursion);
        factors.extend(lucas_factors(term >> 1, subset_recursion));
        factors
    } else if !subset_recursion {
        vec![Factor::Fibonacci(Numeric(term).into()).into()]
    } else {
        let factors_of_term = factorize128(term);
        let mut factors_of_term = factors_of_term
            .into_iter()
            .flat_map(|(key, value)| repeat_n(key, value))
            .collect::<Vec<u128>>();
        let full_set_size = factors_of_term.len();
        let subsets = power_multiset(&mut factors_of_term);
        let mut subset_factors = Vec::with_capacity(subsets.len());
        for subset in subsets {
            if subset.len() < full_set_size && !subset.is_empty() {
                let product: u128 = subset.into_iter().product();
                if product > 2 {
                    subset_factors.push(fibonacci_factors(product, false));
                }
            }
        }
        multiset_union(subset_factors)
    }
}

#[inline]
fn lucas_factors(term: u128, subset_recursion: bool) -> Vec<Rc<Factor>> {
    debug!("lucas_factors: term {term}, subset_recursion {subset_recursion}");
    if term < SMALL_LUCAS_FACTORS.len() as u128 {
        SMALL_LUCAS_FACTORS[term as usize]
            .iter()
            .copied()
            .map(|x| Factor::Numeric(x).into())
            .collect()
    } else if !subset_recursion {
        vec![Factor::Lucas(Numeric(term).into()).into()]
    } else {
        let mut factors_of_term = factorize128(term);
        let power_of_2 = factors_of_term.remove(&2).unwrap_or(0) as u128;
        let mut factors_of_term = factors_of_term
            .into_iter()
            .flat_map(|(key, value)| repeat_n(key, value))
            .collect::<Vec<u128>>();
        let full_set_size = factors_of_term.len();
        let subsets = power_multiset(&mut factors_of_term);
        let mut subset_factors = Vec::with_capacity(subsets.len());
        for subset in subsets {
            if subset.len() < full_set_size && !subset.is_empty() {
                let product = subset.into_iter().product::<u128>() << power_of_2;
                if product > 2 {
                    subset_factors.push(lucas_factors(product, false));
                }
            }
        }
        multiset_union(subset_factors)
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
        return (1, 1);
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

pub fn to_like_powers(left: Rc<Factor>, right: Rc<Factor>, subtract: bool) -> Vec<Rc<Factor>> {
    let mut possible_factors = BTreeMap::new();
    let mut new_left = simplify(left.clone());
    let mut new_right = simplify(right.clone());
    for term in [&mut new_left, &mut new_right] {
        let exponent_u128 = match &**term {
            Factor::Power { exponent, .. } => evaluate_as_u128(&exponent),
            Numeric(a) => {
                let (a, n) = factor_power(*a, 1);
                if n > 1 {
                    *term = Factor::Power {
                        base: Numeric(a).into(),
                        exponent: Numeric(n).into(),
                    }.into();
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
                        factor_exponent.max(possible_factors.get(&factor).copied().unwrap_or(0)),
                    );
                })
        }
    }
    if !subtract {
        possible_factors.remove(&2);
    }
    let total_factors = possible_factors.values().sum::<usize>();
    if total_factors <= 1 {
        return vec![];
    }
    let mut results = Vec::with_capacity(total_factors * 2);
    for (factor, factor_power) in possible_factors {
        if let Ok(left_root) = nth_root_exact(new_left.clone(), factor)
            && let Ok(right_root) = nth_root_exact(new_right.clone(), factor)
        {
            if factor == 2 {
                results.extend(repeat_n(
                    simplify(AddSub {
                        left: left_root.clone().into(),
                        right: right_root.clone().into(),
                        subtract: false,
                    }.into()),
                    factor_power,
                ));
            }
            results.extend(repeat_n(
                simplify(AddSub {
                    left: left_root.into(),
                    right: right_root.into(),
                    subtract,
                }.into()),
                factor_power,
            ));
        }
    }
    results
}
pub fn to_like_powers_recursive_dedup(
    left: Rc<Factor>,
    right: Rc<Factor>,
    subtract: bool,
) -> Vec<Rc<Factor>> {
    let mut results = Vec::new();
    let mut to_expand = count_frequencies(to_like_powers(left.clone(), right.clone(), subtract));
    let mut already_expanded = BTreeSet::new();
    while let Some((factor, exponent)) = to_expand.pop_first() {
        if !already_expanded.contains(&factor) {
            match simplify(factor) {
                AddSub {
                    left: ref factor_left,
                    right: ref factor_right,
                    subtract,
                } => {
                    let subfactors = to_like_powers(factor_left.clone(), factor_right.clone(), subtract);
                    for subfactor in subfactors
                        .into_iter()
                        .filter(|subfactor| subfactor != &factor)
                    {
                        *to_expand.entry(subfactor).or_insert(0) += exponent;
                    }
                    results.extend(repeat_n(factor.clone(), exponent));
                }
                Numeric(n) => {
                    results.extend(find_factors_of_u128(n));
                }
                _ => {
                    results.push(factor.clone());
                }
            }
            already_expanded.insert(factor);
        }
    }
    results
}

pub fn div_exact(product: Rc<Factor>, divisor: Rc<Factor>) -> Result<Rc<Factor>, Rc<Factor>> {
    if product == divisor {
        return Ok(Factor::one());
    }
    if let Some(product_u128) = evaluate_as_u128(&product)
        && let Some(divisor_u128) = evaluate_as_u128(&divisor)
    {
        return match product_u128
            .div_exact(divisor_u128) {
            Some(divided) => Ok(Numeric(divided).into()),
            None => Err(Numeric(product_u128).into())
        };
    }
    match *product {
        Factor::Power {
            ref base,
            ref exponent,
        } => {
            if *base == divisor {
                Ok(simplify(Factor::Power {
                    base: base.clone(),
                    exponent: simplify(AddSub {
                        left: exponent.clone(),
                        right: Factor::one(),
                        subtract: true,
                    }.into())
                }.into()))
            } else if let Some(exponent_u128) = evaluate_as_u128(&exponent)
                && let Ok(divisor_root) = nth_root_exact(divisor, exponent_u128)
            {
                match div_exact(base.clone(), divisor_root) {
                    Ok(divided_base) => {
                        Ok(simplify(Factor::Power {
                            base: divided_base,
                            exponent: Numeric(exponent_u128).into(),
                        }.into()))
                    }
                    Err(_) => {
                        Err(Factor:: Power {
                            base: base.clone(),
                            exponent: Numeric(exponent_u128).into(),
                        }.into())
                    }
                }
            } else {
                Err(product)
            }
        }
        Multiply { ref terms } => {
            let mut divisor_u128 = evaluate_as_u128(&divisor);
            let mut new_terms = terms.clone();
            for (index, term) in new_terms.iter_mut().enumerate() {
                if **term == *divisor {
                    new_terms.remove(index);
                    return Ok(simplify(Multiply { terms: new_terms }.into()));
                }
                if let Some(divisor) = &mut divisor_u128
                    && let Some(term_u128) = evaluate_as_u128(term)
                {
                    let gcd = term_u128.gcd(divisor);
                    if gcd > 1 {
                        *term = Numeric(term_u128 / gcd).into();
                        *divisor /= gcd;
                        if *divisor == 1 {
                            return Ok(simplify(Multiply { terms: new_terms }.into()));
                        }
                    }
                }
            }
            Err(product)
        }
        Factor::Divide {
            ref left,
            ref right,
        } => {
            match div_exact(left.clone(), divisor) {
                Ok(new_left) => Ok(simplify(Factor::Divide {
                    left: new_left,
                    right: right.clone(),
                }.into())),
                Err(_) => Err(product),
            }
        }
        Factor::Factorial(ref term) => {
            if let Some(divisor) = evaluate_as_u128(&divisor)
                && let Some(term) = evaluate_as_u128(term)
            {
                let mut new_term = term;
                while let Some(divisor) = divisor.div_exact(new_term) {
                    new_term -= 1;
                    if divisor == 1 {
                        return Ok(simplify(Factor::Factorial(Numeric(new_term).into()).into()).into());
                    }
                }
                Err(product)
            } else {
                Err(product)
            }
        }
        Factor::Primorial(ref term) => {
            if let Some(mut divisor) = evaluate_as_u128(&divisor)
                && let Some(term) = evaluate_as_u128(term)
            {
                let mut new_term = term;
                while !is_prime(new_term)
                    || divisor
                        .div_exact(new_term)
                        .inspect(|new_divisor| divisor = *new_divisor)
                        .is_some()
                {
                    new_term -= 1;
                    if divisor == 1 {
                        return Ok(simplify(Factor::Primorial(Numeric(new_term).into()).into()));
                    }
                }
                Err(product)
            } else {
                Err(product)
            }
        }
        Factor::BigNumber(ref n) => {
            let mut n_reduced = n.as_ref();
            let mut reduced = false;
            let d_reduced = match &*divisor {
                Numeric(d) => {
                    let mut d = *d;
                    while d.is_multiple_of(10) && n_reduced.ends_with('0') {
                        reduced = true;
                        n_reduced = &n_reduced[0..(n_reduced.len() - 1)];
                        d /= 10;
                    }
                    Some(Numeric(d))
                }
                Factor::BigNumber(d) => {
                    let mut d_reduced = d.as_ref();
                    while d_reduced.ends_with('0') && n_reduced.ends_with('0') {
                        reduced = true;
                        d_reduced = &d_reduced[0..(d_reduced.len() - 1)];
                        n_reduced = &n_reduced[0..(n_reduced.len() - 1)];
                    }
                    Some(d_reduced.into())
                }
                _ => None,
            };
            if reduced && let Some(d_reduced) = d_reduced {
                div_exact(Factor::from(n_reduced).into(), Factor::from(d_reduced).into())
            } else {
                Err(product)
            }
        }
        AddSub {
            ref left,
            ref right,
            subtract,
        } => {
            if let Ok(new_left) = div_exact(left.clone(), divisor.clone())
                    && let Ok(new_right) = div_exact(right.clone(), divisor) {
                Ok(simplify(AddSub {
                    left: new_left.into(),
                    right: new_right.into(),
                    subtract,
                }.into()))
            } else {
                Err(product)
            }
        }
        _ => Err(product)
    }
}

pub fn nth_root_exact(factor: Rc<Factor>, root: u128) -> Result<Rc<Factor>, Rc<Factor>> {
    if root == 1 {
        return Ok(factor);
    }
    if let Some(factor_u128) = evaluate_as_u128(&factor) {
        if factor_u128 == 1 {
            return Ok(Numeric(1).into());
        }
        if let Ok(root_u32) = root.try_into() {
            return factor_u128
                .nth_root_exact(root_u32)
                .map(|x| Numeric(x).into())
                .ok_or(factor);
        }
    }
    match *factor {
        Factor::Power {
            ref base,
            ref exponent,
        } => {
            if evaluate_as_u128(base) == Some(1) {
                return Ok(Factor::one());
            }
            return if let Some(exponent_u128) = evaluate_as_u128(exponent)
                && let Some(reduced_exponent) = exponent_u128.div_exact(root)
            {
                Ok(Factor::Power {
                    base: base.clone(),
                    exponent: Numeric(reduced_exponent).into(),
                }.into())
            } else {
                Err(factor)
            };
        }
        Multiply { ref terms } => {
            let new_terms = terms
                .iter()
                .map(|term| nth_root_exact(term.clone(), root).ok())
                .collect::<Option<Vec<_>>>()
                .ok_or(factor)?;
            return Ok(simplify(Multiply { terms: new_terms }.into()));
        }
        Factor::Divide {
            ref left,
            ref right,
        } => {
            let new_left = nth_root_exact(left.clone(), root)?;
            let new_right = right
                .iter()
                .map(|term| nth_root_exact(term.clone(), root).ok())
                .collect::<Option<Vec<_>>>()
                .ok_or(factor)?;
            return Ok(simplify(Factor::Divide {
                left: new_left.into(),
                right: new_right,
            }.into()));
        }
        _ => {}
    }
    Err(factor)
}

#[inline(always)]
pub(crate) fn find_factors_of_u128(input: u128) -> Vec<Rc<Factor>> {
    debug_assert_ne!(input, 0);
    factorize128(input)
        .into_iter()
        .flat_map(|(factor, power)| repeat_n(Numeric(factor).into(), power))
        .collect()
}

#[inline(always)]
fn estimate_log10_internal(expr: Rc<Factor>) -> (u128, u128) {
    debug!("estimate_log10_internal: {expr}");
    match *expr {
        Numeric(n) => match n {
            0 => {
                warn!("log10 estimate for 0 was requested");
                (0, 0)
            }
            1 => (0, 0),
            n => (n.ilog10() as u128, (n - 1).ilog10() as u128 + 1)
        }
        Factor::BigNumber(ref expr) => {
            let len = expr.as_ref().len();
            ((len - 1) as u128, len as u128)
        }
        Factor::Fibonacci(ref x) | Factor::Lucas(ref x) => {
            // Fibonacci or Lucas number
            let Some(term_number) = evaluate_as_u128(&x) else {
                warn!("Could not parse term number of a Lucas number: {}", x);
                return (0, u128::MAX);
            };
            let est_log = term_number as f64 * 0.20898;
            (est_log.floor() as u128, est_log.ceil() as u128 + 1)
        }
        Factor::Factorial(ref input) => {
            // factorial
            let Some(input) = evaluate_as_u128(input) else {
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
        Factor::Primorial(ref input) => {
            // primorial
            let Some(input) = evaluate_as_u128(&input) else {
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
        Factor::Power { ref base, ref exponent } => {
            let Some(exponent) = evaluate_as_u128(&exponent) else {
                return (0, u128::MAX);
            };
            if let Some(base) = evaluate_as_u128(&base) {
                let lower = (base as f64).log10().next_down() * exponent as f64;
                let upper = (base as f64).log10().next_up() * (exponent as f64).next_up();
                (lower.floor() as u128, upper.ceil() as u128)
            } else {
                let (base_lower, base_upper) = estimate_log10_internal(base.clone());
                (
                    base_lower.saturating_mul(exponent),
                    base_upper.saturating_mul(exponent),
                )
            }
        }
        Factor::Divide { ref left, ref right } => {
            let (num_lower, num_upper) = estimate_log10_internal(left.clone());
            let (denom_lower, denom_upper) = right
                .iter()
                .map(|factor| estimate_log10_internal(factor.clone()))
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
        Multiply { ref terms } => {
            // multiplication
            let (product_lower, product_upper) = terms
                .iter()
                .map(|factor| estimate_log10_internal(factor.clone()))
                .reduce(|(l1, u1), (l2, u2)| {
                    (
                        l1.saturating_add(l2),
                        u1.saturating_add(u2).saturating_add(1),
                    )
                })
                .unwrap();
            (product_lower, product_upper)
        }
        AddSub {
            ref left,
            ref right,
            subtract,
        } => {
            // addition/subtraction
            let (left_lower, left_upper) = estimate_log10_internal(left.clone());
            let (right_lower, right_upper) = estimate_log10_internal(right.clone());
            let combined_lower = if subtract {
                if right_upper >= left_lower - 1 {
                    0
                } else {
                    left_lower.saturating_sub(1)
                }
            } else {
                left_lower.max(right_lower)
            };
            let combined_upper = if subtract {
                left_upper
            } else {
                left_upper.max(right_upper).saturating_add(1)
            };
            (combined_lower, combined_upper)
        }
        Factor::UnknownExpression(_) => (0, u128::MAX),
    }
}

pub(crate) fn estimate_log10(expr: Rc<Factor>) -> (u128, u128) {
    let (lbound, ubound) = estimate_log10_internal(expr.clone());
    if lbound > ubound {
        error!(
            "{expr}: estimate_log10 produced inconsistent bounds: lower bound {lbound}, upper bound {ubound}"
        );
        (0, u128::MAX)
    } else {
        (lbound, ubound)
    }
}

pub(crate) fn evaluate_modulo_as_u128(expr: Rc<Factor>, modulus: u128) -> Option<u128> {
    if let Some(eval) = evaluate_as_u128(&expr) {
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
    match *expr {
        Numeric(n) => Some(n % modulus),
        Factor::BigNumber(_) | Factor::ElidedNumber(_) | Factor::UnknownExpression(_) => None,
        AddSub {
            ref left,
            ref right,
            subtract,
        } => {
            let left = evaluate_modulo_as_u128(left.clone(), modulus)?;
            let right = evaluate_modulo_as_u128(right.clone(), modulus)?;
            if subtract {
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
        Multiply { ref terms } => {
            let mut product: u128 = 1;
            for term in terms.iter() {
                product = product.checked_mul(evaluate_modulo_as_u128(term.clone(), modulus)?)? % modulus;
            }
            Some(product)
        }
        Factor::Divide { ref left, ref right } => {
            let mut result = evaluate_modulo_as_u128(left.clone(), modulus)?;
            for term in right.iter() {
                let term_mod = evaluate_modulo_as_u128(term.clone(), modulus)?;
                match modinv(term_mod, modulus) {
                    Some(inv) => result = (result * inv) % modulus,
                    None => result = result.div_exact(modulus)?,
                }
            }
            Some(result)
        }
        Factor::Power { ref base, ref exponent } => {
            let base_mod = evaluate_modulo_as_u128(base.clone(), modulus)?;
            let exp = evaluate_as_u128(&exponent)?;
            Some(base_mod.powm(exp, &modulus))
        }
        Factor::Fibonacci(ref term) => {
            let term = evaluate_as_u128(&term)?;
            Some(pisano(term, vec![0, 1, 1], modulus))
        }
        Factor::Lucas(ref term) => {
            let term = evaluate_as_u128(&term)?;
            Some(pisano(term, vec![2, 1], modulus))
        }
        Factor::Factorial(ref term) => {
            let term = evaluate_as_u128(&term)?;
            if term >= modulus {
                return Some(0);
            }
            let mut result = 1;
            for i in 2..=term {
                result = (result * i) % modulus;
                if result == 0 {
                    return Some(0);
                }
            }
            Some(result)
        }
        Factor::Primorial(ref term) => {
            let term = evaluate_as_u128(&term)?;
            if term >= modulus {
                return Some(0);
            }
            let mut result = 1;
            for i in 2..=term {
                if is_prime(i) {
                    result = (result * i) % modulus;
                    if result == 0 {
                        return Some(0);
                    }
                }
            }
            Some(result)
        }
    }
}

fn is_prime(val: u128) -> bool {
    SIEVE.with_borrow(|sieve| sieve.is_prime(&val, None)) != No
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

pub(crate) fn simplify(expr: Rc<Factor>) -> Rc<Factor> {
    if let Some(expr_u128) = evaluate_as_u128(&expr) {
        return Numeric(expr_u128).into();
    }
    match *expr {
        Multiply { ref terms } => {
            let new_terms: Vec<Rc<Factor>> = terms
                .iter()
                .flat_map(|term| {
                    if let Multiply { ref terms } = **term {
                        terms.clone()
                    } else {
                        vec![term.clone()]
                    }
                    .into_iter()
                })
                .map(simplify)
                .filter(|term| **term != Numeric(1))
                .sorted_unstable()
                .collect();
            match new_terms.len() {
                0 => Factor::one(),
                1 => new_terms.into_iter().next().unwrap(),
                _ => simplify(Multiply {
                    terms: new_terms.into_iter().collect(),
                }.into()),
            }
        }
        Factor::Divide {
            ref left,
            ref right,
        } => {
            let mut new_left = left.clone();
            let mut new_right = right.clone();
            while let Factor::Divide {
                left: ref left_left,
                right: ref mid,
            } = *new_left {
                let new_right_right = new_right;
                new_right = mid.clone();
                new_right.extend(new_right_right);
                new_left = left_left.clone();
            }
            let new_left = simplify(new_left);
            let mut new_right: Vec<Rc<Factor>> = new_right
                .into_iter()
                .map(simplify)
                .filter(|term| **term != Numeric(1))
                .sorted_unstable()
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
                    right: new_right,
                }.into()
            }
        }
        Factor::Power { ref base, ref exponent } => {
            let mut new_base = simplify(base.clone());
            let mut new_exponent = simplify(exponent.clone());
            if let Numeric(new_base_u128) = *new_base {
                if new_base_u128 == 1 {
                    return Factor::one();
                }
                if let Some(new_exponent_u128) = evaluate_as_u128(&new_exponent) {
                    let (factored_base_u128, factored_exponent_u128) =
                        factor_power(new_base_u128, new_exponent_u128);
                    if factored_exponent_u128 != new_exponent_u128 {
                        new_base = Numeric(factored_base_u128).into();
                        new_exponent = Numeric(factored_exponent_u128).into();
                    }
                }
            }
            match *new_exponent {
                Numeric(0) => Factor::one(),
                Numeric(1) => new_base,
                _ => Factor::Power {
                    base: new_base.into(),
                    exponent: new_exponent.into(),
                }.into(),
            }
        }
        Factor::Factorial(ref term) | Factor::Primorial(ref term) => match **term {
            Numeric(0) | Numeric(1) => Factor::one(),
            _ => expr,
        },
        AddSub {
            ref left,
            ref right,
            subtract,
        } => {
            let mut left = simplify(left.clone());
            let mut right = simplify(right.clone());
            match left.cmp(&right) {
                Ordering::Less => {}
                Ordering::Equal => return if subtract {
                        Numeric(0)
                    } else {
                        simplify(Multiply {
                            terms: vec![left, Factor::two()],
                        }.into())
                    },
                Ordering::Greater => {
                    if !subtract && left > right {
                        swap(&mut left, &mut right);
                    }
                }
            }
            AddSub { left, right, subtract }.into()
        }
        _ => expr
    }
}

pub(crate) fn evaluate_as_u128(expr: &Factor) -> Option<u128> {
    match expr {
        Numeric(n) => Some(*n),
        Factor::BigNumber(_) => None,
        Factor::Lucas(term) => {
            let term = evaluate_as_u128(term)?;
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
            let term = evaluate_as_u128(term)?;
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
        Factor::Factorial(term) => {
            let term = evaluate_as_u128(term)?;
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
            let term = evaluate_as_u128(term)?;
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
        Factor::Power { base, exponent } => match evaluate_as_u128(base)? {
            0 => Some(0),
            1 => Some(1),
            base => base.checked_pow(u32::try_from(evaluate_as_u128(exponent)?).ok()?),
        },
        Factor::Divide { left, right } => {
            let mut result = evaluate_as_u128(left)?;
            for term in right.iter() {
                result = result.checked_div_exact(evaluate_as_u128(term)?)?;
            }
            Some(result)
        }
        Multiply { terms } => {
            let mut result = 1u128;
            for term in terms.iter() {
                result = result.checked_mul(evaluate_as_u128(term)?)?;
            }
            Some(result)
        }
        AddSub {
            left,
            right,
            subtract,
        } => {
            let left = evaluate_as_u128(left)?;
            let right = evaluate_as_u128(right)?;
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
fn find_factors(expr: Rc<Factor>) -> Vec<Rc<Factor>> {
    info!("find_factors: {expr}");
    if let Some(n) = evaluate_as_u128(&expr) {
        return find_factors_of_u128(n);
    }
    match *expr {
        Numeric(n) => find_factors_of_u128(n),
        Factor::BigNumber(ref expr) => factor_big_num(expr.clone()),
        Factor::Lucas(ref term) => {
            // Lucas number
            let Some(term_number) = evaluate_as_u128(&term) else {
                warn!("Could not parse term number of a Lucas number: {}", term);
                return vec![expr];
            };
            lucas_factors(term_number, true)
        }
        Factor::Fibonacci(ref term) => {
            // Fibonacci number
            let Some(term_number) = evaluate_as_u128(&term) else {
                warn!(
                    "Could not parse term number of a Fibonacci number: {}",
                    term
                );
                return vec![expr];
            };
            fibonacci_factors(term_number, true)
        }
        Factor::Factorial(ref term) => {
            // factorial
            let Some(input) = evaluate_as_u128(&term) else {
                warn!("Could not parse input to factorial function: {}", term);
                return vec![expr];
            };
            let mut factors = Vec::new();
            for i in 2..=input {
                factors.extend(find_factors_of_u128(i));
            }
            factors
        }
        Factor::Primorial(ref term) => {
            // primorial
            let Some(input) = evaluate_as_u128(&term) else {
                warn!("Could not parse input to primorial function: {}", term);
                return vec![expr];
            };
            let mut factors = Vec::new();
            for i in 2..=input {
                if is_prime(i) {
                    factors.push(Numeric(i).into());
                }
            }
            factors
        }
        Factor::ElidedNumber(ref n) => match n.chars().last() {
            Some('0') => vec![Factor::two(), Factor::five()],
            Some('5') => vec![Factor::five()],
            Some('2' | '4' | '6' | '8') => vec![Factor::two()],
            Some('1' | '3' | '7' | '9') => vec![],
            x => {
                error!("Invalid last digit: {x:?}");
                vec![]
            }
        },
        Factor::Power { ref base, ref exponent } => {
            let power = evaluate_as_u128(&exponent)
                .unwrap_or(MAX_REPEATS)
                .min(MAX_REPEATS) as usize;
            let base_factors = find_factors(base.clone());
            repeat_n(base_factors, power).flatten().collect()
        }
        Factor::Divide { ref left, ref right } => {
            // division
            let mut left_recursive_factors = vec![];
            let left_remaining_factors = find_factors(left.clone());
            let mut left_remaining_factors = count_frequencies(left_remaining_factors);
            while let Some((factor, exponent)) = left_remaining_factors.pop_first() {
                let subfactors = find_factors(factor.clone());
                subfactors
                    .into_iter()
                    .filter(|subfactor| *subfactor != factor)
                    .for_each(|subfactor| {
                        *left_remaining_factors.entry(subfactor).or_insert(0) += exponent
                    });
                left_recursive_factors.push(factor);
            }
            let mut right_remaining_factors = right.clone();
            while let Some(factor) = right_remaining_factors.pop() {
                let subfactors = find_factors(factor.clone());
                if (subfactors.is_empty() || (subfactors.len() == 1 && subfactors[0] == factor))
                    && let Some((index, remove)) = left_recursive_factors
                        .iter_mut()
                        .enumerate()
                        .flat_map(|(index, left_factor)| {
                            if *left_factor == factor {
                                return Some((index, true));
                            }
                            match div_exact(take(left_factor), factor.clone()) {
                                Ok(quotient) => {
                                    *left_factor = quotient;
                                    Some((index, false))
                                }
                                Err(returned_left_factor) => {
                                    *left_factor = returned_left_factor;
                                    None
                                }
                            }
                        })
                        .next()
                {
                    if remove {
                        left_recursive_factors.remove(index);
                    }
                } else {
                    right_remaining_factors.extend(
                        subfactors
                            .into_iter()
                            .filter(|subfactor| *subfactor != factor),
                    );
                }
            }
            left_recursive_factors
        }
        Multiply { ref terms } => {
            // multiplication
            let mut factors = Vec::new();
            for term in terms.into_iter() {
                let term_factors = find_factors(term.clone());
                if term_factors.is_empty() {
                    factors.push(term.clone());
                } else {
                    factors.extend(term_factors);
                }
            }
            factors
        }
        AddSub {
            ref left,
            ref right,
            subtract,
        } => {
            let mut factors = Vec::with_capacity(SMALL_PRIMES.len());
            for prime in SMALL_PRIMES {
                let mut power = prime as u128;
                let prime_factor: Rc<Factor> = Numeric(prime as u128).into();
                while evaluate_modulo_as_u128(expr.clone(), power) == Some(0) {
                    factors.push(prime_factor.clone());
                    let Some(new_power) = power.checked_mul(prime as u128) else {
                        break;
                    };
                    power = new_power;
                }
            }
            factors = multiset_union(vec![
                factors,
                to_like_powers_recursive_dedup(left.clone(), right.clone(), subtract),
                find_common_factors(left.clone(), right.clone()),
            ]);
            let cofactors: Vec<_> = factors
                .iter()
                .unique()
                .flat_map(|factor: &Rc<Factor>| {
                    div_exact(expr.clone(), factor.clone())
                    .ok()
                })
                .collect();
            factors = multiset_union(vec![factors, cofactors]);
            factors
        }
        Factor::UnknownExpression(_) => vec![expr],
    }
}

fn factor_big_num(expr: BigNumber) -> Vec<Rc<Factor>> {
    let mut factors = Vec::new();
    let mut expr_short = expr.as_ref();
    while expr_short != "0"
        && let Some(stripped) = expr_short.strip_suffix('0')
    {
        factors.push(Factor::two());
        factors.push(Factor::five());
        expr_short = stripped;
    }
    if let Ok(num) = expr_short.parse::<u128>() {
        factors.extend(find_factors_of_u128(num));
    } else {
        match expr_short.chars().last() {
            Some('5') => factors.push(Factor::five()),
            Some('2' | '4' | '6' | '8') => factors.push(Factor::two()),
            Some('1' | '3' | '7' | '9') => {
                factors.push(Factor::from(expr_short).into());
            }
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
                factors.extend([Factor::three(), Factor::three()]);
            }
            3 | 6 => {
                factors.push(Factor::three());
            }
            _ => {}
        }
        if expr_short.len() >= 2 {
            factors.push(Factor::from(expr_short).into());
        } else {
            // All other single-digit numbers are handled by the 2, 5, 3 and 9 cases
            match expr_short {
                "4" => {
                    factors.push(Factor::two());
                }
                "7" => {
                    factors.push(Numeric(7).into());
                }
                "8" => {
                    factors.extend([Factor::two(), Factor::two()]);
                }
                _ => {}
            }
        }
    }
    factors
}

#[inline]
fn find_common_factors(expr1: Rc<Factor>, expr2: Rc<Factor>) -> Vec<Rc<Factor>> {
    let num1 = evaluate_as_u128(&expr1);
    if num1 == Some(1) {
        return vec![];
    }
    let num2 = evaluate_as_u128(&expr2);
    if num2 == Some(1) {
        return vec![];
    }
    if let Some(num1) = num1
        && let Some(num2) = num2
    {
        find_factors_of_u128(num1.gcd(&num2))
    } else {
        let expr1_factors = find_factors(expr1);
        if expr1_factors.is_empty() {
            return vec![];
        }
        let expr2_factors = find_factors(expr2);
        multiset_intersection(expr1_factors, expr2_factors)
    }
}

/// Returns all unique, nontrivial factors we can find.
#[inline(always)]
pub fn find_unique_factors(expr: Rc<Factor>) -> Box<[Rc<Factor>]> {
    let mut factors = find_factors(expr.clone());
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

#[derive(Clone, Default, Debug)]
pub struct ProcessedStatusApiResponse {
    pub status: Option<NumberStatus>,
    pub factors: Box<[Rc<Factor>]>,
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
    use alloc::rc::Rc;
    use crate::algebraic::Factor::Numeric;
    use crate::algebraic::{
        Factor, SMALL_FIBONACCI_FACTORS, SMALL_LUCAS_FACTORS,
        evaluate_as_u128, factor_power, fibonacci_factors, lucas_factors, modinv,
        multiset_intersection, multiset_union, power_multiset,
    };
    use itertools::Itertools;
    use std::iter::repeat_n;

    fn find_factors(input: &str) -> Vec<Factor> {
        crate::algebraic::find_factors(Factor::from(input).into()).into_iter().map(Rc::unwrap_or_clone).collect()
    }

    #[test]
    fn test_precedence() {
        assert_eq!(
            &Factor::from("(3^7396-928)/3309349849490834480566907-1").to_string(),
            "((((3)^(7396))-(928))/(3309349849490834480566907))-(1)"
        );
        assert_eq!(evaluate_as_u128(&"(3^7-6)/727".into()), Some(3));
    }

    #[test]
    fn test_division() {
        let factors = find_factors("(2^625+1)/(2^5+1)".into());
        println!("{}", factors.iter().join(","));
        assert!(!factors.contains(&3.into()));
        assert!(
            !find_factors("lucas(604203)/lucas(201401)/4".into()).contains(&"lucas(201401)".into())
        );
    }

    #[test]
    fn test_anbc() {
        let expr = format!("{}^9*3+3", u128::MAX);
        let factors = find_factors(&expr);
        println!("{}", factors.iter().join(", "));
        assert!(factors.contains(&3.into()));
        assert!(factors.contains(&format!("{}^9+1", u128::MAX).into()));
    }

    #[test]
    fn test_anbc_2() {
        let factors = find_factors("(6^200600+1)/17".into());
        println!("{}", factors.iter().join(", "));

        // Should contain (6^8+1)/17
        assert!(factors.contains(&98801.into()));

        // Shouldn't contain 6^5+1
        assert!(!factors.contains(&(6u128.pow(5) + 1).into()));
        assert!(!factors.contains(&7.into()));
        assert!(!factors.contains(&11.into()));
        assert!(!factors.contains(&101.into()));
    }

    #[test]
    fn test_anbc_3() {
        let factors = find_factors("6^1337*5-15".into());

        assert!(factors.contains(&3.into())); // common factor of a^x and c
        assert!(factors.contains(&5.into())); // common factor of b and c
    }

    #[test]
    fn test_anb_minus_c() {
        let expr = format!("{}^24-1", u128::MAX);
        let factors = find_factors(&expr);
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
    fn test_axbx() {
        let factors = find_factors("(1297^400-901^400)/3".into());
        println!("{}", factors.iter().sorted().unique().join(","));
        assert!(factors.contains(&Numeric(2)));
        assert!(factors.contains(&Numeric(5)));
        assert!(factors.contains(&Numeric(11)));
        assert!(factors.contains(&"1297^100-901^100".into()));
        assert!(factors.contains(&"1297^80-901^80".into()));
        assert!(factors.contains(&"1297^100+901^100".into()));
        assert!(!factors.contains(&"1297^80+901^80".into()));
        let factors = find_factors("1297^390-901^390".into());
        println!("{}", factors.iter().sorted().unique().join(","));
        assert!(
            factors
                .iter()
                .any(|factor| matches!(factor, Numeric(n) if n.is_multiple_of(2)))
        );
        assert!(
            factors
                .iter()
                .any(|factor| matches!(factor, Numeric(n) if n.is_multiple_of(3)))
        );
        assert!(
            !factors
                .iter()
                .any(|factor| matches!(factor, Numeric(n) if n.is_multiple_of(5)))
        );
        assert!(
            factors
                .iter()
                .any(|factor| matches!(factor, Numeric(n) if n.is_multiple_of(11)))
        );
        assert!(factors.contains(&"1297^130-901^130".into()));
        assert!(factors.contains(&"1297^195-901^195".into()));
        assert!(!factors.contains(&"1297^130+901^130".into()));
        assert!(factors.contains(&"1297^195+901^195".into()));
    }
    #[test]
    fn test_axby() {
        let factors = find_factors("1297^1234-901^1".into());
        println!("{}", factors.iter().sorted().unique().join(","));
        assert!(factors.contains(&Numeric(2)));
        assert!(factors.contains(&Numeric(3)));

        // These expressions are negative but should not crash
        find_factors("1297^1-901^123".into());
        find_factors("901^1-1297^1".into());
    }

    #[test]
    fn test_chain() {
        let factors = find_factors("2^8+3*5-1".into());
        assert!(factors.contains(&Numeric(2)));
    }

    #[test]
    fn test_chain_2() {
        let factors = find_factors("(2^9+1)^2*7^2/361".into());
        assert!(factors.contains(&Numeric(3)));
        assert!(factors.contains(&Numeric(7)));
        assert!(!factors.contains(&Numeric(19)));
    }

    #[test]
    fn test_mul_chain() {
        let factors = find_factors("2^8*3*5".into());
        assert!(factors.contains(&Numeric(2)));
        assert!(factors.contains(&Numeric(3)));
        assert!(factors.contains(&Numeric(5)));
    }

    #[test]
    fn test_div_chain() {
        let factors = find_factors("210/2/5".into());
        assert!(factors.contains(&Numeric(3)));
        assert!(factors.contains(&Numeric(7)));
        assert!(!factors.contains(&Numeric(2)));
        assert!(!factors.contains(&Numeric(5)));
    }

    #[test]
    fn test_mixed_chain() {
        let expr = format!(
            "(2^256-1)*(3^200+1)*(10^50)*((12^368-1)^2)/20/1{}",
            &repeat_n('0', 50).collect::<String>()
        );
        let factors = find_factors(&expr);
        println!("{}", factors.iter().join(","));
        assert!(!factors.contains(&Numeric(2)));
        assert!(factors.contains(&Numeric(3)));
        // assert!(!factors.contains(&Numeric(5)));
        assert!(factors.contains(&Numeric(11)));
    }

    #[test]
    fn test_addition_chain() {
        let factors = find_factors("7^5432+3*7^4321+7^321+7^21".into());
        println!("{}", factors.iter().join(","));
        assert!(factors.contains(&Numeric(2)));
        assert!(factors.contains(&Numeric(7)));
        let factors = find_factors("7^5432+3*7^4321+7^321+7^21+1".into());
        assert!(!factors.contains(&Numeric(2)));
        assert!(!factors.contains(&Numeric(7)));
        let factors = find_factors("3*7^5432+7^4321+7^321+1".into());
        assert!(factors.contains(&Numeric(2)));
        assert!(!factors.contains(&Numeric(7)));
        let factors = find_factors("7^5432-7^4321-3*7^321-1".into());
        assert!(factors.contains(&Numeric(2)));
        assert!(!factors.contains(&Numeric(7)));
    }

    #[test]
    fn test_power() {
        let factors = find_factors("(2^7-1)^2".into());
        assert_eq!(factors, Vec::<Factor>::from([Numeric(127), Numeric(127)]));
    }

    #[test]
    fn test_power_associativity() {
        let expr = "2^3^4".into();

        assert_eq!(evaluate_as_u128(&expr), Some(1 << 81));
    }

    #[test]
    fn test_division_associativity() {
        let expr = "20/5/2".into();

        assert_eq!(evaluate_as_u128(&expr), Some(2));
    }

    #[test]
    fn test_stack_depth() {
        // unsafe { backtrace_on_stack_overflow::enable() };
        let expr = repeat_n("(2^9+1)", 1 << 16).join("*");
        find_factors(&expr);
        let expr = Rc::new(Factor::from(expr));
        crate::algebraic::estimate_log10_internal(expr.clone());
        evaluate_as_u128(&expr);

    }

    #[test]
    fn test_stack_depth_2() {
        const PRIMORIAL: u128 = 2 * 3 * 5 * 7 * 11 * 13 * 17 * 19;
        lucas_factors(PRIMORIAL, true);
        fibonacci_factors(PRIMORIAL, true);
    }

    #[test]
    fn test_parse() {
        let factors = find_factors("I(17#)".into());
        // lucas_factors(PRIMORIAL, true);
        assert!(factors.contains(&Numeric(13)));
    }

    #[test]
    fn test_nested_parens() {
        let factors = find_factors("(12^((2^7-1)^2)-1)/88750555799".into());
        println!("{}", factors.iter().join(","));
        assert!(factors.contains(&Numeric(11)));
        assert!(factors.contains(&"12^127-1".into()));
    }

    #[test]
    fn test_multiple_hashes() {
        assert_eq!(evaluate_as_u128(&"2##".into()), Some(6)); // 2## = 6; (2#)# = 2
        assert_eq!(evaluate_as_u128(&"2###".into()), Some(30)); // 2### = (2##)# = 30; (2#)## = 6

        // 2#### = (2##)## = 30030
        assert_eq!(evaluate_as_u128(&"2####".into()), Some(30030));
        // (3#)### = 30029#
        // (3##)## = 113#
        // (3###)# = 6469693230#

        println!("{}", find_factors("92##".into()).into_iter().join(","));
    }

    #[test]
    fn test_m_precedence() {
        assert_eq!(evaluate_as_u128(&"M7^2".into()), Some(127 * 127));
        assert_eq!(evaluate_as_u128(&"M7*5".into()), Some(127 * 5));
        assert_eq!(evaluate_as_u128(&"M5!".into()), Some((1..=31).product())); // (M5)!
        assert_eq!(
            evaluate_as_u128(&"M5#".into()),
            Some(2 * 3 * 5 * 7 * 11 * 13 * 17 * 19 * 23 * 29 * 31)
        ); // (M5)#
    }

    #[test]
    fn test_factor_power() {
        assert_eq!(
            factor_power(5474401089420219382077155933569751763, 16),
            (3, 16 * 77)
        );
        // (3^77)^16+1
        let factors = find_factors("5474401089420219382077155933569751763^16+1".into());
        println!("{}", factors.iter().join(","));
        // factors of 3^16+1
        // assert!(factors.contains(&Numeric(2)));
        assert!(factors.contains(&"3^176+1".into()));
        assert!(factors.contains(&"3^112+1".into()));
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
                assert!(factors.contains(&(Numeric(*factor).into())));
            }
        }
    }

    #[test]
    fn test_fibonacci() {
        let factors = fibonacci_factors(5040, true);
        let larger_factors = factors
            .iter()
            .cloned()
            .filter(|f| if let Numeric(n) = **f { n > 7 } else { true })
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
                assert!(factors.contains(&Numeric(*factor).into()));
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
        let mut union = multiset_union(vec![multiset_1, multiset_2]);
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
    fn test_estimate_log10() {
        fn estimate_log10_internal(input: &str) -> (u128, u128) {
            crate::algebraic::estimate_log10_internal(Factor::from(input).into())
        }

        let (lower, upper) = estimate_log10_internal("99");
        assert_eq!(lower, 1);
        assert_eq!(upper, 2);
        let (lower, upper) = estimate_log10_internal("100");
        assert_eq!(lower, 2);
        assert_eq!(upper, 2);
        let (lower, upper) = estimate_log10_internal("101");
        assert_eq!(lower, 2);
        assert_eq!(upper, 3);
        let (lower, upper) = estimate_log10_internal(
            &("1".to_string() + &repeat_n('0', 50).collect::<String>()));
        assert_eq!(lower, 50);
        assert!(upper == 50 || upper == 51);
        let (lower, upper) = estimate_log10_internal(
            &(repeat_n('9', 50).collect::<String>())
        );
        assert_eq!(lower, 49);
        assert!(upper == 49 || upper == 50);
        let (lower, upper) = estimate_log10_internal("I1234".into());
        assert_eq!(lower, 257);
        assert!(upper == 258 || upper == 259);
        let (lower, upper) = estimate_log10_internal("lucas(1234)".into());
        assert_eq!(lower, 257);
        assert!(upper == 258 || upper == 259);
        let (lower, upper) = estimate_log10_internal("2^607-1".into());
        assert!(lower == 182 || lower == 181);
        assert_eq!(upper, 183);
        let (lower, upper) = estimate_log10_internal("10^200-1".into());
        assert!(lower == 198 || lower == 199);
        assert!(upper == 200 || upper == 201);
        let (lower, upper) = estimate_log10_internal("10^200+1".into());
        assert!(lower == 199 || lower == 200);
        assert!(upper == 201 || upper == 202);
        let (lower, upper) = estimate_log10_internal("10^200*31-1".into());
        assert!(lower >= 199);
        assert!(lower <= 201);
        assert!(upper >= 202);
        assert!(lower <= 204);
        let (lower, upper) = estimate_log10_internal("100!".into());
        assert_eq!(lower, 157);
        assert_eq!(upper, 158);
        let (lower, upper) = estimate_log10_internal("100#".into());
        assert!(lower <= 36);
        assert!(upper >= 37);
        assert!(upper <= 44);
        let (lower, upper) = estimate_log10_internal("20+30".into());
        assert_eq!(lower, 1);
        assert!(upper == 2 || upper == 3);
        let (lower, upper) = estimate_log10_internal("30-19".into());
        assert!(lower <= 1);
        assert_eq!(upper, 2);
        let (lower, upper) = estimate_log10_internal("11*11".into());
        assert_eq!(lower, 2);
        assert!(upper >= 3);
        let (lower, upper) = estimate_log10_internal("(2^769-1)/1591805393".into());
        assert!(lower >= 219 && lower <= 222);
        assert!(upper >= 223 && upper <= 225);
        let (lower, upper) = estimate_log10_internal("3^5000-4^2001".into());
        assert!(lower == 2385 || lower == 2384);
        assert!(upper == 2386 || upper == 2387);
    }

    #[test]
    fn test_evaluate_as_u128() {
        assert_eq!(evaluate_as_u128(&"2^127-1".into()), Some(i128::MAX as u128));
        assert_eq!(evaluate_as_u128(&"(5^6+1)^2-1".into()), Some(244171875));
        assert_eq!(evaluate_as_u128(&"3^3+4^4+5^5".into()), Some(3408));
    }

    #[test]
    fn test_may_be_proper_divisor_of() {
        fn may_be_proper_divisor_of(left: &str, right: &str) -> bool {
            Factor::from(left).may_be_proper_divisor_of(&Factor::from(right))
        }
        assert!(may_be_proper_divisor_of("123", "369^2"));
        assert!(!may_be_proper_divisor_of("2", "34567"));
        assert!(may_be_proper_divisor_of("2", "345-67"));
        assert!(!may_be_proper_divisor_of("12345", "54321"));
        assert!(!may_be_proper_divisor_of("12345", "12345"));
        assert!(!may_be_proper_divisor_of("54321", "12345"));
        assert!(!may_be_proper_divisor_of(
            "123456789123456789123456789123456789123456789",
            "123456789123456789123456789123456789123456789/3"
        ));
        assert!(!may_be_proper_divisor_of("2^1234-1", "(2^1234-1)/3"));
    }
}
