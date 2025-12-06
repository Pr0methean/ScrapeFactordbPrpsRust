use crate::algebraic::Factor::{AddSub, Multiply, Numeric};
use crate::graph::EntryId;
use crate::net::BigNumber;
use crate::{MAX_ID_EQUAL_TO_VALUE, NumberLength, write_bignum, frame_sync};
use hipstr::HipStr;
use itertools::Itertools;
use log::{debug, error, info, warn};
use num_integer::Integer;
use num_modular::{ModularCoreOps, ModularPow};
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
use std::mem::{replace, swap};
use std::sync::Arc;
use async_backtrace::location;

static SMALL_FIBONACCI_FACTORS: [&[NumericFactor]; 199] = [
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

static SMALL_LUCAS_FACTORS: [&[NumericFactor]; 202] = [
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

pub type NumericFactor = u128;
pub type SignedNumericFactor = i128;

#[derive(Clone, Debug, Hash, Eq, PartialEq, Ord, PartialOrd)]
pub enum Factor {
    Numeric(NumericFactor),
    BigNumber(BigNumber),
    ElidedNumber(HipStr<'static>),
    UnknownExpression(HipStr<'static>),
    AddSub {
        left: Arc<Factor>,
        right: Arc<Factor>,
        subtract: bool,
    },
    Multiply {
        terms: BTreeMap<Arc<Factor>, NumberLength>,
    },
    Divide {
        left: Arc<Factor>,
        right: BTreeMap<Arc<Factor>, NumberLength>,
    },
    Power {
        base: Arc<Factor>,
        exponent: Arc<Factor>,
    },
    Fibonacci(Arc<Factor>),
    Lucas(Arc<Factor>),
    Factorial(Arc<Factor>),
    Primorial(Arc<Factor>),
}

impl Default for Factor {
    fn default() -> Self {
        Numeric(1)
    }
}

peg::parser! {
  pub grammar expression_parser() for str {
    pub rule number() -> Factor
      = n:$(['0'..='9']+) { n.parse::<NumericFactor>().map(Numeric).unwrap_or_else(|_| Factor::BigNumber(n.into())) }

    #[cache_left_rec]
    pub rule arithmetic() -> Factor = precedence!{
      x:(@) "+" y:@ { AddSub { left: x.into(), right: y.into(), subtract: false } }
      x:(@) "-" y:@ { AddSub { left: x.into(), right: y.into(), subtract: true } }
      --
      x:(@) "/" y:@ {
        let mut x = x;
        let mut y = y;
        if let Factor::Divide { ref mut right, .. } = x {
            *right.entry(y.into()).or_insert(0) += 1;
            x
        } else if let Factor::Divide { ref mut left, ref mut right } = y {
            let old_left = core::mem::take(left);
            *left = Multiply { terms: [(old_left, 1), (x.into(), 1)].into() }.into();
            y
        } else {
            Factor::Divide { left: x.into(), right: [(y.into(), 1)].into() }
        }
      }
      --
      x:(@) "*" y:@ {
        let mut x = x;
        let mut y = y;
        if let Multiply { ref mut terms, .. } = x {
            *terms.entry(y.into()).or_insert(0) += 1;
            x
        } else if let Multiply { ref mut terms, .. } = y {
            *terms.entry(x.into()).or_insert(0) += 1;
            y
        } else if x == y {
            Multiply { terms: [(x.into(), 2)].into() }
        } else {
            Multiply { terms: [(x.into(), 1), (y.into(), 1)].into() }
        }
      }
      --
      x:@ "^" y:(@) { Factor::Power { base: x.into(), exponent: y.into() } }
      --
      x:@ "^" y:number() {
                if let Some(y_numeric) = evaluate_as_numeric(&y).and_then(|y| NumberLength::try_from(y).ok()) {
                  Multiply { terms: [(x.into(), y_numeric)].into() }
                } else {
                  Factor::Power { base: x.into(), exponent: y.into() }
                }
      }
      --
      x:@ "!" { Factor::Factorial(x.into()) }
      x:@ y:$("#"+) {
                    let hashes = y.len();
                    let mut output = x;
                    for _ in 0..(hashes >> 1) {
                        output = Factor::Primorial(Numeric(SIEVE.with_borrow_mut(|sieve| sieve.nth_prime(evaluate_as_numeric(&output).unwrap() as u64)) as NumericFactor).into());
                    }
                    if !hashes.is_multiple_of(2) {
                        output = Factor::Primorial(output.into())
                    };
                    output
                }
      --
      "M" x:@ { AddSub { left: Factor::Power { base: Factor::two(), exponent: Arc::new(x) }.into(), right: Factor::one(), subtract: true } }
      --
      "I" x:@ { Factor::Fibonacci(x.into()) }
      --
      "lucas(" x:arithmetic() ")" { Factor::Lucas(x.into()) }
      --
      n:$(['0'..='9']+ "..." ['0'..='9']+) { Factor::ElidedNumber(n.into()) }
      --
      n:number() { n }
      --
      "(" e:arithmetic() ")" { e }
    }
  }
}

impl Factor {
    thread_local! {
        static ONE: Arc<Factor> = Arc::new(Numeric(1));
        static TWO: Arc<Factor> = Arc::new(Numeric(2));
        static THREE: Arc<Factor> = Arc::new(Numeric(3));
        static FIVE: Arc<Factor> = Arc::new(Numeric(5));
    }
    pub fn one() -> Arc<Factor> {
        Factor::ONE.with(Arc::clone)
    }
    pub fn two() -> Arc<Factor> {
        Factor::TWO.with(Arc::clone)
    }
    pub fn three() -> Arc<Factor> {
        Factor::THREE.with(Arc::clone)
    }
    pub fn five() -> Arc<Factor> {
        Factor::FIVE.with(Arc::clone)
    }
    #[inline(always)]
    pub fn known_id(&self) -> Option<EntryId> {
        if let Numeric(n) = self
            && *n <= MAX_ID_EQUAL_TO_VALUE
        {
            Some(*n)
        } else {
            None
        }
    }
    #[inline(always)]
    pub fn as_numeric(&self) -> Option<NumericFactor> {
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
    pub fn as_str_non_numeric(&self) -> Option<HipStr<'static>> {
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
        if let Some(n) = evaluate_as_numeric(self)
            && let Some(o) = evaluate_as_numeric(other)
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
        if let Factor::Divide { left, right } = self
            && !(Multiply {
                terms: right.clone(),
            }
            .may_be_proper_divisor_of(left))
        {
            // Can't be an integer, therefore can't be a divisor
            return false;
        }
        if let Factor::Divide { left, right } = other
            && !(Multiply {
                terms: right.clone(),
            }
            .may_be_proper_divisor_of(left))
        {
            // other can't be an integer, so it has no divisors
            return false;
        }
        if let Multiply { terms } = self
            && terms
                .keys()
                .any(|term| !term.may_be_proper_divisor_of(other))
        {
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

impl From<NumericFactor> for Factor {
    #[inline(always)]
    fn from(value: NumericFactor) -> Self {
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
                    .map(|factor| Arc::unwrap_or_clone(simplify(factor.into())))
                    .unwrap_or_else(|e| {
                        error!("Error parsing expression {value}: {e}");
                        Factor::UnknownExpression(value.into())
                    })
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
                "({left}{}{right})",
                if *subtract { '-' } else { '+' }
            )),
            Multiply { terms } => f.write_fmt(format_args!(
                "({})",
                terms
                    .iter()
                    .map(|(term, exponent)| if *exponent == 1 {
                        term.to_string()
                    } else {
                        format!("({term})^{exponent}")
                    })
                    .join("*")
            )),
            Factor::Divide { left, right } => f.write_fmt(format_args!(
                "({left}/{})",
                right
                    .iter()
                    .map(|(term, exponent)| if *exponent == 1 {
                        term.to_string()
                    } else {
                        format!("({term})^{exponent}")
                    })
                    .join("/")
            )),
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
fn count_frequencies<T: Eq + Ord>(vec: Vec<T>) -> BTreeMap<T, NumberLength> {
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
            intersection_vec.extend(repeat_n(item, min_count as usize));
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
        .flat_map(|(item, count)| repeat_n(item, count as usize))
        .collect()
}

#[inline]
fn fibonacci_factors(term: NumericFactor, subset_recursion: bool) -> Vec<Arc<Factor>> {
    debug!("fibonacci_factors: term {term}, subset_recursion {subset_recursion}");
    if term < SMALL_FIBONACCI_FACTORS.len() as NumericFactor {
        SMALL_FIBONACCI_FACTORS[term as usize]
            .iter()
            .copied()
            .map(|x| Numeric(x).into())
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
            .collect::<Vec<NumericFactor>>();
        let full_set_size = factors_of_term.len();
        let subsets = power_multiset(&mut factors_of_term);
        let mut subset_factors = Vec::with_capacity(subsets.len());
        for subset in subsets {
            if subset.len() < full_set_size && !subset.is_empty() {
                let product: NumericFactor = subset.into_iter().product();
                if product > 2 {
                    subset_factors.push(fibonacci_factors(product, false));
                }
            }
        }
        multiset_union(subset_factors)
    }
}

#[inline]
fn lucas_factors(term: NumericFactor, subset_recursion: bool) -> Vec<Arc<Factor>> {
    debug!("lucas_factors: term {term}, subset_recursion {subset_recursion}");
    if term < SMALL_LUCAS_FACTORS.len() as NumericFactor {
        SMALL_LUCAS_FACTORS[term as usize]
            .iter()
            .copied()
            .map(|x| Numeric(x).into())
            .collect()
    } else if !subset_recursion {
        vec![Factor::Lucas(Numeric(term).into()).into()]
    } else {
        let mut factors_of_term = factorize128(term);
        let power_of_2 = factors_of_term.remove(&2).unwrap_or(0) as NumericFactor;
        let mut factors_of_term = factors_of_term
            .into_iter()
            .flat_map(|(key, value)| repeat_n(key, value))
            .collect::<Vec<NumericFactor>>();
        let full_set_size = factors_of_term.len();
        let subsets = power_multiset(&mut factors_of_term);
        let mut subset_factors = Vec::with_capacity(subsets.len());
        for subset in subsets {
            if subset.len() < full_set_size && !subset.is_empty() {
                let product = subset.into_iter().product::<NumericFactor>() << power_of_2;
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
fn modinv(a: NumericFactor, m: NumericFactor) -> Option<NumericFactor> {
    let mut t: SignedNumericFactor = 0;
    let mut newt: SignedNumericFactor = 1;
    let m: SignedNumericFactor = m.try_into().ok()?;
    let mut r = m;
    let mut newr: SignedNumericFactor = a.try_into().ok()?;

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
        t += m;
    }

    t.try_into().ok()
}

// Maximum number of times a factor will be repeated when raised to a power, to limit memory usage.
const MAX_REPEATS: usize = 16;

fn factor_power(a: NumericFactor, n: NumericFactor) -> (NumericFactor, NumericFactor) {
    if a == 1 {
        return (1, 1);
    }
    // A NumericFactor can't be a 128th or higher power
    for prime in [
        2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89,
        97, 101, 103, 107, 109, 113, 127,
    ] {
        if let Some(root) = a.nth_root_exact(prime as u32) {
            return match n.checked_mul(prime as NumericFactor) {
                Some(product) => factor_power(root, product),
                None => (a, n),
            };
        }
    }
    (a, n)
}

pub fn to_like_powers(left: Arc<Factor>, right: Arc<Factor>, subtract: bool) -> Vec<Arc<Factor>> {
    let mut possible_factors = BTreeMap::new();
    let mut new_left = simplify(Arc::clone(&left));
    let mut new_right = simplify(Arc::clone(&right));
    for term in [&mut new_left, &mut new_right] {
        let exponent_numeric = match &**term {
            Factor::Power { exponent, .. } => evaluate_as_numeric(exponent),
            Numeric(a) => {
                let (a, n) = factor_power(*a, 1);
                if n > 1 {
                    *term = Multiply {
                        terms: [(Numeric(a).into(), n as NumberLength)].into(),
                    }
                    .into();
                    Some(n)
                } else {
                    None
                }
            }
            Multiply { terms } => {
                // Return GCD of exponents without modifying the term
                // nth_root_exact will handle the exponent division later
                terms.values().copied().reduce(|x, y| x.gcd(&y)).map(NumericFactor::from)
            }
            _ => evaluate_as_numeric(term),
        };
        if let Some(exponent_numeric) = exponent_numeric {
            factorize128(exponent_numeric)
                .into_iter()
                .for_each(|(factor, factor_exponent)| {
                    possible_factors.insert(
                        factor,
                        factor_exponent.max(possible_factors.get(&factor).copied().unwrap_or(0)),
                    );
                })
        }
    }
    let total_factors = possible_factors.values().sum::<usize>();
    if total_factors <= 1 {
        return vec![];
    }
    let mut results = Vec::with_capacity(total_factors * 2);
    for (factor, _factor_power) in possible_factors {
        if let Ok(factor) = NumberLength::try_from(factor)
            && let Some(left_root) = nth_root_exact(&new_left, factor)
            && let Some(right_root) = nth_root_exact(&new_right, factor)
        {
            if subtract {
                results.push(simplify(
                    AddSub {
                        left: Arc::clone(&left_root),
                        right: Arc::clone(&right_root),
                        subtract: true,
                    }
                    .into(),
                ));
                if factor == 2 {
                    results.push(simplify(
                        AddSub {
                            left: left_root,
                            right: right_root,
                            subtract: false,
                        }
                        .into(),
                    ));
                }
            } else if factor != 2 {
                results.push(simplify(
                    AddSub {
                        left: left_root,
                        right: right_root,
                        subtract: false,
                    }
                    .into(),
                ));
            }
        }
    }
    results
}
pub fn to_like_powers_recursive_dedup(
    left: Arc<Factor>,
    right: Arc<Factor>,
    subtract: bool,
) -> Vec<Arc<Factor>> {
    let mut results = Vec::new();
    let mut to_expand = count_frequencies(to_like_powers(
        Arc::clone(&left),
        Arc::clone(&right),
        subtract,
    ));
    let mut already_expanded = BTreeSet::new();
    while let Some((factor, exponent)) = to_expand.pop_first() {
        if !already_expanded.contains(&factor) {
            match *simplify(Arc::clone(&factor)) {
                AddSub {
                    left: ref factor_left,
                    right: ref factor_right,
                    subtract,
                } => {
                    let subfactors =
                        to_like_powers(Arc::clone(factor_left), Arc::clone(factor_right), subtract);
                    for subfactor in subfactors
                        .into_iter()
                        .filter(|subfactor| subfactor != &factor)
                    {
                        *to_expand.entry(subfactor).or_insert(0) += exponent;
                    }
                    results.extend(repeat_n(Arc::clone(&factor), exponent as usize));
                }
                Numeric(n) => {
                    if n > (1 << 64) && !is_prime(n) {
                        results.push(Numeric(n).into());
                    } else {
                        results.extend(find_factors_of_numeric(n));
                    }
                }
                _ => {
                    results.push(Arc::clone(&factor));
                }
            }
            already_expanded.insert(factor);
        }
    }
    results
}

pub fn div_exact(product: &Arc<Factor>, divisor: &Arc<Factor>) -> Option<Arc<Factor>> {
    if product == divisor {
        return Some(Factor::one());
    }
    if let Some(product_numeric) = evaluate_as_numeric(product)
        && let Some(divisor_numeric) = evaluate_as_numeric(divisor)
    {
        return product_numeric
            .div_exact(divisor_numeric)
            .map(|divided| Numeric(divided).into());
    }
    match **product {
        Factor::Power {
            ref base,
            ref exponent,
        } => {
            if base == divisor {
                // x^y / x -> x^(y-1)
                Some(simplify(
                    Factor::Power {
                        base: Arc::clone(base),
                        exponent: simplify(
                            AddSub {
                                left: Arc::clone(exponent),
                                right: Factor::one(),
                                subtract: true,
                            }
                            .into(),
                        ),
                    }
                    .into(),
                ))
            } else if let Some(exponent_numeric) = evaluate_as_numeric(exponent)
                && let Ok(exponent_numeric) = NumberLength::try_from(exponent_numeric)
                && let Some(divisor_root) = nth_root_exact(divisor, exponent_numeric)
            {
                Some(simplify(
                    Multiply {
                        terms: [(div_exact(base, &divisor_root)?, exponent_numeric)].into(),
                    }
                    .into(),
                ))
            } else {
                None
            }
        }
        Multiply { ref terms } => {
            let mut divisor_terms = match **divisor {
                Multiply { ref terms } => terms.clone(),
                _ => [(Arc::clone(divisor), 1)].into(),
            };
            let mut new_terms = terms.clone();
            for (term, exponent) in new_terms.iter_mut() {
                if let Some(divisor_exponent) = divisor_terms.get_mut(term) {
                    let min_exponent = (*divisor_exponent).min(*exponent);
                    *divisor_exponent -= min_exponent;
                    if *divisor_exponent == 0 {
                        divisor_terms.remove(term);
                    }
                    *exponent -= min_exponent;
                }
            }
            new_terms.retain(|_, exponent| *exponent != 0);
            divisor_terms.retain(|_, exponent| *exponent != 0);
            if divisor_terms.is_empty() {
                return Some(simplify(Multiply { terms: new_terms }.into()));
            }
            if new_terms.is_empty() {
                return None;
            }
            let divisor_numeric: NumericFactor = divisor_terms
                .into_iter()
                .map(|(term, exponent)| {
                    evaluate_as_numeric(&term).and_then(|numeric| numeric.checked_pow(exponent))
                })
                .collect::<Option<Vec<_>>>()?
                .into_iter()
                .product();
            let product_numeric: NumericFactor = terms
                .iter()
                .map(|(term, exponent)| {
                    evaluate_as_numeric(term).and_then(|numeric| numeric.checked_pow(*exponent))
                })
                .collect::<Option<Vec<_>>>()?
                .into_iter()
                .product();
            Some(Numeric(product_numeric.div_exact(divisor_numeric)?).into())
        }
        Factor::Divide {
            ref left,
            ref right,
        } => Some(simplify(
            Factor::Divide {
                left: div_exact(left, divisor)?,
                right: right.clone(),
            }
            .into(),
        )),
        Factor::Factorial(ref term) => {
            if let Some(divisor) = evaluate_as_numeric(divisor)
                && let Some(term) = evaluate_as_numeric(term)
            {
                let mut new_term = term;
                while let Some(divisor) = divisor.div_exact(new_term) {
                    new_term -= 1;
                    if divisor == 1 {
                        return Some(simplify(Factor::Factorial(Numeric(new_term).into()).into()));
                    }
                }
            }
            None
        }
        Factor::Primorial(ref term) => {
            if let Some(mut divisor) = evaluate_as_numeric(divisor)
                && let Some(term) = evaluate_as_numeric(term)
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
                        return Some(simplify(Factor::Primorial(Numeric(new_term).into()).into()));
                    }
                }
            }
            None
        }
        Factor::BigNumber(ref n) => {
            let mut n_reduced = n.as_ref();
            let mut reduced = false;
            let d_reduced = match **divisor {
                Numeric(d) => {
                    let mut d_reduced = d;
                    while d_reduced.is_multiple_of(10) && n_reduced.ends_with('0') {
                        reduced = true;
                        n_reduced = &n_reduced[0..(n_reduced.len() - 1)];
                        d_reduced /= 10;
                    }
                    Some(Numeric(d_reduced))
                }
                Factor::BigNumber(ref d) => {
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
                div_exact(&Factor::from(n_reduced).into(), &d_reduced.into())
            } else {
                None
            }
        }
        AddSub {
            ref left,
            ref right,
            subtract,
        } => {
            if let Some(new_left) = div_exact(left, divisor)
                && let Some(new_right) = div_exact(right, divisor)
            {
                Some(simplify(
                    AddSub {
                        left: new_left,
                        right: new_right,
                        subtract,
                    }
                    .into(),
                ))
            } else {
                None
            }
        }
        _ => None,
    }
}

pub fn nth_root_exact(factor: &Arc<Factor>, root: NumberLength) -> Option<Arc<Factor>> {
    if root == 1 {
        return Some(Arc::clone(factor));
    }
    if let Some(factor_numeric) = evaluate_as_numeric(factor) {
        if factor_numeric == 1 {
            return Some(Factor::one());
        }
        return factor_numeric
            .nth_root_exact(root)
            .map(|x| Numeric(x).into());
    }
    match **factor {
        Factor::Power {
            ref base,
            ref exponent,
        } => {
            if evaluate_as_numeric(base) == Some(1) {
                return Some(Factor::one());
            }
            return if let Some(exponent_numeric) = evaluate_as_numeric(exponent)
                && let Some(reduced_exponent) = exponent_numeric.div_exact(root.into())
            {
                Some(
                    Multiply {
                        terms: [(Arc::clone(base), reduced_exponent as NumberLength)].into(),
                    }
                    .into(),
                )
            } else {
                None
            };
        }
        Multiply { ref terms } => {
            let new_terms = nth_root_of_product(terms, root)?;
            return Some(simplify(Multiply { terms: new_terms }.into()));
        }
        Factor::Divide {
            ref left,
            ref right,
        } => {
            let new_left = nth_root_exact(left, root)?;
            let new_right = nth_root_of_product(right, root)?;
            return Some(simplify(
                Factor::Divide {
                    left: new_left,
                    right: new_right,
                }
                .into(),
            ));
        }
        _ => {}
    }
    None
}

fn nth_root_of_product(
    terms: &BTreeMap<Arc<Factor>, NumberLength>,
    root: NumberLength,
) -> Option<BTreeMap<Arc<Factor>, NumberLength>> {
    let root = NumberLength::try_from(root).ok()?;
    terms
        .iter()
        .map(|(term, exponent)| {
            nth_root_exact(term, root)
                .map(|x| (x, *exponent))
                .or_else(|| Some((nth_root_exact(term, root.div_exact(*exponent)?)?, 1)))
                .or_else(|| Some((Arc::clone(term), exponent.div_exact(root)?)))
        })
        .collect()
}

#[inline(always)]
pub(crate) fn find_factors_of_numeric(input: NumericFactor) -> Vec<Arc<Factor>> {
    debug_assert_ne!(input, 0);
    factorize128(input)
        .into_iter()
        .flat_map(|(factor, power)| repeat_n(Numeric(factor).into(), power))
        .collect()
}

#[inline(always)]
fn estimate_log10_internal(expr: Arc<Factor>) -> (NumberLength, NumberLength) {
    debug!("estimate_log10_internal: {expr}");
    match *expr {
        Numeric(n) => match n {
            0 => {
                warn!("log10 estimate for 0 was requested");
                (0, 0)
            }
            1 => (0, 0),
            n => (
                n.ilog10() as NumberLength,
                (n - 1).ilog10() as NumberLength + 1,
            ),
        },
        Factor::BigNumber(ref expr) => {
            let len = expr.as_ref().len();
            ((len - 1) as NumberLength, len as NumberLength)
        }
        Factor::Fibonacci(ref x) | Factor::Lucas(ref x) => {
            // Fibonacci or Lucas number
            let Some(term_number) = evaluate_as_numeric(x) else {
                warn!("Could not parse term number of a Lucas number: {}", x);
                return (0, NumberLength::MAX);
            };
            let est_log = term_number as f64 * 0.20898;
            (
                est_log.floor() as NumberLength,
                est_log.ceil() as NumberLength + 1,
            )
        }
        Factor::Factorial(ref input) => {
            // factorial
            let Some(input) = evaluate_as_numeric(input) else {
                warn!("Could not parse input to a factorial: {}", input);
                return (0, NumberLength::MAX);
            };
            let (ln_factorial, _) = ((input + 1) as f64).ln_gamma();

            // LN_10 is already rounded up
            let log_factorial_lower_bound = ln_factorial.next_down() / LN_10;
            let log_factorial_upper_bound = ln_factorial.next_up() / LN_10.next_down();

            (
                log_factorial_lower_bound.floor() as NumberLength,
                log_factorial_upper_bound.ceil() as NumberLength,
            )
        }
        Factor::Primorial(ref input) => {
            // primorial
            let Some(input) = evaluate_as_numeric(input) else {
                warn!("Could not parse input to a factorial: {}", input);
                return (0, NumberLength::MAX);
            };

            // Lower bound is from
            // Rosser, J. Barkley; Schoenfeld, Lowell (1962-03-01).
            // "Approximate formulas for some functions of prime numbers".
            // Illinois Journal of Mathematics 6 (1), p. 70
            // https://projecteuclid.org/journalArticle/Download?urlId=10.1215%2Fijm%2F1255631807
            // (p. 7 of PDF)
            let lower_bound = if input >= 563 {
                (input as f64 * (1.0 / (2.0 * (input as f64).ln())) / LN_10).ceil() as NumberLength
            } else if input >= 41 {
                (input as f64 * (1.0 / (input as f64).ln()) / LN_10.next_down()).ceil()
                    as NumberLength
            } else {
                0
            };
            let upper_bound = (1.01624 / LN_10 * input as f64).floor() as NumberLength;
            (lower_bound, upper_bound)
        }
        Factor::ElidedNumber(_) => {
            // Elided numbers from factordb are always at least 51 digits
            (50, NumberLength::MAX)
        }
        Factor::Power {
            ref base,
            ref exponent,
        } => {
            let Some(exponent) = evaluate_as_numeric(exponent)
                .and_then(|exponent| NumberLength::try_from(exponent).ok())
            else {
                return (0, NumberLength::MAX);
            };
            if let Some(base) = evaluate_as_numeric(base) {
                let lower = (base as f64).log10().next_down() * exponent as f64;
                let upper = (base as f64).log10().next_up() * (exponent as f64).next_up();
                (lower.floor() as NumberLength, upper.ceil() as NumberLength)
            } else {
                let (base_lower, base_upper) = estimate_log10_internal(base.clone());
                (
                    base_lower.saturating_mul(exponent),
                    base_upper.saturating_mul(exponent),
                )
            }
        }
        Factor::Divide {
            ref left,
            ref right,
        } => {
            let (num_lower, num_upper) = estimate_log10_internal(left.clone());
            let (denom_lower, denom_upper) = estimate_log10_of_product(right);
            let lower = num_lower.saturating_sub(denom_upper.saturating_add(1));
            let upper = num_upper.saturating_sub(denom_lower.saturating_sub(1));
            (lower, upper)
        }
        Multiply { ref terms } => {
            // multiplication
            let (product_lower, product_upper) = estimate_log10_of_product(terms);
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
        Factor::UnknownExpression(_) => (0, NumberLength::MAX),
    }
}

fn estimate_log10_of_product(
    terms: &BTreeMap<Arc<Factor>, NumberLength>,
) -> (NumberLength, NumberLength) {
    let mut lower: NumberLength = 0;
    let mut upper: NumberLength = 0;
    for (term, exponent) in terms {
        let (power_lower, power_upper) = match *exponent {
            0 => (0, 0),
            1 => estimate_log10_internal(Arc::clone(term)),
            x => estimate_log10_internal(
                Factor::Power {
                    base: Arc::clone(term),
                    exponent: Numeric(x as NumericFactor).into(),
                }
                .into(),
            ),
        };
        lower = lower.saturating_add(power_lower);
        upper = upper.saturating_add(power_upper).saturating_add(1);
    }
    (lower, upper - 1)
}

pub(crate) fn estimate_log10(expr: Arc<Factor>) -> (NumberLength, NumberLength) {
    let (lbound, ubound) = estimate_log10_internal(expr.clone());
    if lbound > ubound {
        error!(
            "{expr}: estimate_log10 produced inconsistent bounds: lower bound {lbound}, upper bound {ubound}"
        );
        (0, NumberLength::MAX)
    } else {
        (lbound, ubound)
    }
}

pub(crate) fn modulo_as_numeric(
    expr: &Arc<Factor>,
    modulus: NumericFactor,
) -> Option<NumericFactor> {
    if let Some(eval) = evaluate_as_numeric(expr) {
        return Some(eval % modulus);
    }
    match modulus {
        0 => {
            warn!("Attempted to evaluate {expr} modulo 0");
            None
        }
        1 => Some(0),
        _ => match **expr {
            Numeric(n) => Some(n % modulus),
            Factor::BigNumber(_) => {
                if (modulus == 2 || modulus == 5)
                    && let Some(last_digit) = expr.last_digit()
                {
                    Some(last_digit as NumericFactor % modulus)
                } else {
                    None
                }
            }
            Factor::ElidedNumber(_) | Factor::UnknownExpression(_) => None,
            AddSub {
                ref left,
                ref right,
                subtract,
            } => {
                let left = modulo_as_numeric(left, modulus)?;
                let right = modulo_as_numeric(right, modulus)?;
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
                let mut product: NumericFactor = 1;
                for (term, exponent) in terms.iter() {
                    product = product.checked_mul(
                        modulo_as_numeric(term, modulus)?
                            .powm(*exponent as NumericFactor, &modulus),
                    )? % modulus;
                }
                Some(product)
            }
            Factor::Divide {
                ref left,
                ref right,
            } => {
                let mut result = modulo_as_numeric(left, modulus)?;
                for (term, exponent) in right.iter() {
                    let term_mod = modulo_as_numeric(term, modulus)?
                        .powm(*exponent as NumericFactor, &modulus);
                    match modinv(term_mod, modulus) {
                        Some(inv) => result = result.mulm(inv, &modulus),
                        None => result = result.div_exact(modulus)?,
                    }
                }
                Some(result)
            }
            Factor::Power {
                ref base,
                ref exponent,
            } => {
                let base_mod = modulo_as_numeric(base, modulus)?;
                let exp = evaluate_as_numeric(exponent)?;
                Some(base_mod.powm(exp, &modulus))
            }
            Factor::Fibonacci(ref term) => {
                let term = evaluate_as_numeric(term)?;
                Some(pisano(term, vec![0, 1, 1], modulus))
            }
            Factor::Lucas(ref term) => {
                let term = evaluate_as_numeric(term)?;
                Some(pisano(term, vec![2, 1], modulus))
            }
            Factor::Factorial(ref term) => {
                let term = evaluate_as_numeric(term)?;
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
                let term = evaluate_as_numeric(term)?;
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
        },
    }
}

fn is_prime(val: NumericFactor) -> bool {
    SIEVE.with_borrow(|sieve| sieve.is_prime(&val, None)) != No
}

fn pisano(
    term: NumericFactor,
    mut sequence: Vec<NumericFactor>,
    modulus: NumericFactor,
) -> NumericFactor {
    let mut zeros = 0; // don't count the initial 0th term for Fibonacci sequence
    loop {
        if sequence.len() as NumericFactor == term + 1 {
            return *sequence.last().unwrap();
        }
        let next_term = (sequence[sequence.len() - 2] + sequence[sequence.len() - 2]) % modulus;
        if next_term == 0 {
            zeros += 1;
        }
        if zeros == 4 && next_term == sequence[0] {
            return sequence[(term % (sequence.len() as NumericFactor)) as usize];
        }
        sequence.push(next_term);
    }
}

pub(crate) fn simplify(expr: Arc<Factor>) -> Arc<Factor> {
    if let Some(expr_numeric) = evaluate_as_numeric(&expr) {
        return if matches!(*expr, Numeric(_)) {
            expr
        } else {
            Numeric(expr_numeric).into()
        };
    }
    match *expr {
        Multiply { ref terms } => {
            let mut new_terms = BTreeMap::new();
            for (term, exponent) in terms.iter() {
                if let Multiply { ref terms } = **term {
                    terms
                        .clone()
                        .into_iter()
                        .map(|(term, term_exponent)| (simplify(term), term_exponent * exponent))
                        .for_each(|(term, term_exponent)| {
                            *new_terms.entry(term).or_insert(0) += term_exponent
                        });
                } else {
                    *new_terms.entry(Arc::clone(term)).or_insert(0) += exponent;
                }
            }
            new_terms.retain(|factor, exponent| *factor != Factor::one() && *exponent != 0);
            match new_terms.len() {
                0 => Factor::one(),
                1 => {
                    let (factor, power) = new_terms.into_iter().next().unwrap();
                    if power == 1 {
                        factor
                    } else {
                        Multiply { terms: [(factor, power)].into() }.into()
                    }
                }
                _ => Multiply { terms: new_terms }.into(),
            }
        }
        Factor::Divide {
            ref left,
            ref right,
        } => {
            let mut new_left = Arc::clone(left);
            let mut new_right = right.clone();
            while let Factor::Divide {
                left: ref left_left,
                right: ref mid,
            } = *new_left
            {
                // (left_left / mid) / right
                let new_right_right = replace(&mut new_right, mid.clone());
                new_right.extend(new_right_right);
                new_left = Arc::clone(left_left);
                // left_left / (mid * right)
            }
            let mut new_left = simplify(new_left);
            let mut cloned_right = new_right.clone();
            for (term, exponent) in new_right {
                let simplified = simplify(Arc::clone(&term));
                if let Multiply { ref terms } = *simplified {
                    cloned_right.remove(&term);
                    for (subterm, subterm_exponent) in terms {
                        *cloned_right
                            .entry(simplify(Arc::clone(subterm)))
                            .or_insert(0) += exponent * subterm_exponent;
                    }
                } else if simplified != term {
                    *cloned_right.entry(simplified).or_insert(0) +=
                        cloned_right.remove(&term).unwrap();
                }
            }
            cloned_right.retain(|_, exponent| *exponent != 0);
            if let Some(exponent) = cloned_right.get_mut(&new_left) {
                *exponent -= 1;
                new_left = Factor::one();
            }
            if cloned_right.is_empty() {
                new_left
            } else {
                Factor::Divide {
                    left: new_left,
                    right: cloned_right,
                }
                .into()
            }
        }
        Factor::Power {
            ref base,
            ref exponent,
        } => {
            let mut new_base = simplify(Arc::clone(base));
            let mut new_exponent = simplify(Arc::clone(exponent));
            if let Numeric(new_base_numeric) = *new_base {
                if new_base_numeric == 1 {
                    return Factor::one();
                }
                if let Some(new_exponent_numeric) = evaluate_as_numeric(&new_exponent) {
                    let (factored_base, factored_exponent) =
                        factor_power(new_base_numeric, new_exponent_numeric);
                    if factored_exponent != new_exponent_numeric {
                        new_base = Numeric(factored_base).into();
                        new_exponent = Numeric(factored_exponent).into();
                    }
                }
            }
            match *new_exponent {
                Numeric(0) => Factor::one(),
                Numeric(1) => new_base,
                Numeric(n) => Multiply {
                    terms: [(new_base, n as NumberLength)].into()
                }.into(),
                _ => Factor::Power {
                    base: new_base,
                    exponent: new_exponent,
                }
                .into(),
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
            let mut left = simplify(Arc::clone(left));
            let mut right = simplify(Arc::clone(right));
            match left.cmp(&right) {
                Ordering::Less => {}
                Ordering::Equal => {
                    return if subtract {
                        Numeric(0).into()
                    } else {
                        simplify(
                            Multiply {
                                terms: [(left, 1), (Factor::two(), 1)].into(),
                            }
                            .into(),
                        )
                    };
                }
                Ordering::Greater => {
                    if !subtract && left > right {
                        swap(&mut left, &mut right);
                    }
                }
            }
            AddSub {
                left,
                right,
                subtract,
            }
            .into()
        }
        _ => expr,
    }
}

pub(crate) fn evaluate_as_numeric(expr: &Factor) -> Option<NumericFactor> {
    match expr {
        Numeric(n) => Some(*n),
        Factor::BigNumber(_) => None,
        Factor::Lucas(term) => {
            let term = evaluate_as_numeric(term)?;
            match term {
                0 => Some(2),
                1 => Some(1),
                185.. => None,
                n => {
                    let mut a: NumericFactor = 2;
                    let mut b: NumericFactor = 1;
                    let mut result: NumericFactor = 0;

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
            let term = evaluate_as_numeric(term)?;
            match term {
                0 => Some(0),
                1 | 2 => Some(1),
                186.. => None,
                n => {
                    let mut a: NumericFactor = 1;
                    let mut b: NumericFactor = 1;
                    let mut result: NumericFactor = 0;
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
            let term = evaluate_as_numeric(term)?;
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
            let term = evaluate_as_numeric(term)?;
            match term {
                0 | 1 => Some(1),
                103.. => None,
                x => Some(
                    // SMALL_PRIMES always has all the primes we need
                    SMALL_PRIMES
                        .iter()
                        .copied()
                        .map(NumericFactor::from)
                        .take_while(|p| *p <= x)
                        .product(),
                ),
            }
        }
        Factor::ElidedNumber(_) => None,
        Factor::Power { base, exponent } => match evaluate_as_numeric(base)? {
            0 => Some(0),
            1 => Some(1),
            base => base.checked_pow(u32::try_from(evaluate_as_numeric(exponent)?).ok()?),
        },
        Factor::Divide { left, right } => {
            let mut result = evaluate_as_numeric(left)?;
            for (term, exponent) in right.iter() {
                result =
                    result.checked_div_exact(evaluate_as_numeric(term)?.checked_pow(*exponent)?)?;
            }
            Some(result)
        }
        Multiply { terms } => {
            let mut result: NumericFactor = 1;
            for (term, exponent) in terms.iter() {
                result = result.checked_mul(evaluate_as_numeric(term)?.checked_pow(*exponent)?)?;
            }
            Some(result)
        }
        AddSub {
            left,
            right,
            subtract,
        } => {
            let left = evaluate_as_numeric(left)?;
            let right = evaluate_as_numeric(right)?;
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
fn find_factors(expr: Arc<Factor>) -> Vec<Arc<Factor>> {
    let expr_string = format!("find_factors: {expr}");
    info!("{}", expr_string);
    frame_sync(location!().named(expr_string), || {
        if let Some(n) = evaluate_as_numeric(&expr) {
            return find_factors_of_numeric(n);
        }
        match *expr {
            Numeric(n) => find_factors_of_numeric(n),
            Factor::BigNumber(ref expr) => factor_big_num(expr.clone()),
            Factor::Lucas(ref term) => {
                // Lucas number
                let Some(term_number) = evaluate_as_numeric(term) else {
                    warn!("Could not parse term number of a Lucas number: {}", term);
                    return vec![expr];
                };
                lucas_factors(term_number, true)
            }
            Factor::Fibonacci(ref term) => {
                // Fibonacci number
                let Some(term_number) = evaluate_as_numeric(term) else {
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
                let Some(input) = evaluate_as_numeric(term) else {
                    warn!("Could not parse input to factorial function: {}", term);
                    return vec![expr];
                };
                let mut factors = Vec::new();
                for i in 2..=input {
                    factors.extend(find_factors_of_numeric(i));
                }
                factors
            }
            Factor::Primorial(ref term) => {
                // primorial
                let Some(input) = evaluate_as_numeric(term) else {
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
            Factor::Power {
                ref base,
                ref exponent,
            } => {
                let power = evaluate_as_numeric(exponent)
                    .and_then(|power| usize::try_from(power).ok())
                    .unwrap_or(MAX_REPEATS)
                    .min(MAX_REPEATS);
                let base_factors = find_factors(base.clone());
                repeat_n(base_factors, power).flatten().collect()
            }
            Factor::Divide {
                ref left,
                ref right,
            } => {
                // division
                let mut left_recursive_factors = BTreeMap::new();
                let left_remaining_factors = find_factors(left.clone());
                let mut left_remaining_factors = count_frequencies(left_remaining_factors);
                while let Some((factor, exponent)) = left_remaining_factors.pop_first() {
                    let subfactors = if factor == expr {
                        vec![Arc::clone(&factor)]
                    } else {
                        find_factors(factor.clone())
                    };
                    subfactors
                        .into_iter()
                        .filter(|subfactor| *subfactor != factor)
                        .for_each(|subfactor| {
                            *left_remaining_factors.entry(subfactor).or_insert(0) += exponent
                        });
                    *left_recursive_factors.entry(factor).or_insert(0) += exponent;
                }
                let mut right_remaining_factors = right.clone();
                while let Some((factor, exponent)) = right_remaining_factors.pop_last() {
                    let subfactors = find_factors(Arc::clone(&factor));
                    if subfactors.is_empty() || (subfactors.len() == 1 && subfactors[0] == factor) {
                        if let Some(left_exponent) = left_recursive_factors.get_mut(&factor) {
                            let min_exponent = (*left_exponent).min(exponent);
                            *left_exponent -= min_exponent;
                            if min_exponent != exponent && min_exponent != 0 {
                                right_remaining_factors.insert(factor, exponent - min_exponent);
                            }
                        }
                    } else {
                        for (subfactor, subfactor_exponent) in count_frequencies(subfactors) {
                            *right_remaining_factors.entry(subfactor).or_insert(0) +=
                                subfactor_exponent;
                        }
                    }
                }
                left_recursive_factors
                    .into_iter()
                    .flat_map(|(factor, exponent)| repeat_n(factor, exponent as usize))
                    .collect()
            }
            Multiply { ref terms } => {
                // multiplication
                let mut factors = Vec::new();
                for (term, exponent) in terms {
                    let term_factors = find_factors(Arc::clone(term));
                    if term_factors.is_empty() {
                        factors.extend(repeat_n(Arc::clone(term), *exponent as usize));
                    } else {
                        factors.extend(repeat_n(term_factors, *exponent as usize).flatten());
                    }
                }
                factors
            }
            AddSub {
                ref left,
                ref right,
                subtract,
            } => {
                let algebraic =
                    to_like_powers_recursive_dedup(Arc::clone(left), Arc::clone(right), subtract);
                if !algebraic.is_empty() {
                    return algebraic;
                }
                let mut factors = find_common_factors(Arc::clone(left), Arc::clone(right));
                for prime in SMALL_PRIMES {
                    let mut power = prime as NumericFactor;
                    let prime_factor: Arc<Factor> = Numeric(power).into();
                    while modulo_as_numeric(&expr, power) == Some(0) {
                        factors.push(prime_factor.clone());
                        let Some(new_power) = power.checked_mul(prime as NumericFactor) else {
                            break;
                        };
                        power = new_power;
                    }
                }
                factors = multiset_union(vec![
                    factors,
                    to_like_powers_recursive_dedup(Arc::clone(left), Arc::clone(right), subtract),
                    find_common_factors(Arc::clone(left), Arc::clone(right)),
                ]);
                let cofactors: Vec<_> = factors
                    .iter()
                    .unique()
                    .flat_map(|factor: &Arc<Factor>| div_exact(&expr, factor))
                    .collect();
                factors = multiset_union(vec![factors, cofactors]);
                factors
            }
            Factor::UnknownExpression(_) => vec![expr],
        }
    })
}

fn factor_big_num(expr: BigNumber) -> Vec<Arc<Factor>> {
    let mut factors = Vec::new();
    let mut expr_short = expr.as_ref();
    while expr_short != "0"
        && let Some(stripped) = expr_short.strip_suffix('0')
    {
        factors.push(Factor::two());
        factors.push(Factor::five());
        expr_short = stripped;
    }
    if let Ok(num) = expr_short.parse::<NumericFactor>() {
        factors.extend(find_factors_of_numeric(num));
    } else {
        let mut divisor_map = BTreeMap::new();
        match expr_short.chars().last() {
            Some('5') => *divisor_map.entry(Factor::five()).or_insert(0) += 1,
            Some('2' | '4' | '6' | '8') => *divisor_map.entry(Factor::two()).or_insert(0) += 1,
            // '0' is handled by strip_suffix
            _ => {}
        }
        let sum_of_digits: NumericFactor = expr_short
            .chars()
            .map(|digit| digit.to_digit(10).unwrap() as NumericFactor)
            .sum();
        match sum_of_digits % 9 {
            0 => {
                *divisor_map.entry(Factor::three()).or_insert(0) += 2;
            }
            3 | 6 => {
                *divisor_map.entry(Factor::three()).or_insert(0) += 1;
            }
            _ => {}
        }

        if divisor_map.is_empty() {
            factors.push(Factor::from(expr_short).into());
        } else {
            let original = Factor::from(expr_short).into();
            factors.extend(
                divisor_map.iter().flat_map(|(factor, exponent)| {
                    repeat_n(Arc::clone(factor), *exponent as usize)
                }),
            );
            factors.push(
                Factor::Divide {
                    left: original,
                    right: divisor_map,
                }
                .into(),
            );
        }
    }
    factors
}

#[inline]
fn find_common_factors(expr1: Arc<Factor>, expr2: Arc<Factor>) -> Vec<Arc<Factor>> {
    let num1 = evaluate_as_numeric(&expr1);
    if num1 == Some(1) {
        return vec![];
    }
    let num2 = evaluate_as_numeric(&expr2);
    if num2 == Some(1) {
        return vec![];
    }
    if let Some(num1) = num1
        && let Some(num2) = num2
    {
        find_factors_of_numeric(num1.gcd(&num2))
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
pub fn find_unique_factors(expr: Arc<Factor>) -> Box<[Arc<Factor>]> {
    let mut factors = find_factors(expr.clone());
    factors.retain(|f| f.as_numeric() != Some(1) && f.may_be_proper_divisor_of(&expr));
    factors.sort_unstable();
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

#[cfg(test)]
mod tests {
    use crate::NumberLength;
    use crate::algebraic::Factor::Numeric;
    use crate::algebraic::{
        Factor, NumericFactor, SMALL_FIBONACCI_FACTORS, SMALL_LUCAS_FACTORS, evaluate_as_numeric,
        factor_power, fibonacci_factors, lucas_factors, modinv, multiset_intersection,
        multiset_union, power_multiset,
    };
    use itertools::Itertools;
    use std::iter::repeat_n;
    use std::sync::Arc;

    fn find_factors(input: &str) -> Vec<Factor> {
        crate::algebraic::find_factors(Factor::from(input).into())
            .into_iter()
            .map(Arc::unwrap_or_clone)
            .collect()
    }

    #[test]
    fn test_precedence() {
        assert_eq!(
            &Factor::from("(3^7396-928)/3309349849490834480566907-1").to_string(),
            "(((((3)^7396)-928)/3309349849490834480566907)-1)"
        );
        assert_eq!(evaluate_as_numeric(&"(3^7-6)/727".into()), Some(3));
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
        let expr = format!("{}^9*3+3", NumericFactor::MAX);
        let factors = find_factors(&expr);
        println!("{}", factors.iter().join(", "));
        assert!(factors.contains(&3.into()));
        assert!(factors.contains(&format!("{}^9+1", NumericFactor::MAX).into()));
    }

    #[test]
    fn test_anbc_2() {
        let factors = find_factors("(6^200600+1)/17".into());
        println!("{}", factors.iter().join(", "));

        // Should contain (6^8+1)/17
        assert!(factors.contains(&98801.into()));

        // Shouldn't contain 6^5+1
        assert!(!factors.contains(&((6 as NumericFactor).pow(5) + 1).into()));
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
        let expr = format!("{}^24-1", NumericFactor::MAX);
        let factors = find_factors(&expr);
        println!("{}", factors.iter().join(", "));
        assert!(factors.contains(&format!("{}^12-1", NumericFactor::MAX).into()));
        assert!(factors.contains(&format!("{}^12+1", NumericFactor::MAX).into()));
        assert!(factors.contains(&format!("{}^8-1", NumericFactor::MAX).into()));
        assert!(!factors.contains(&format!("{}^8+1", NumericFactor::MAX).into()));
        assert!(factors.contains(&format!("{}^6+1", NumericFactor::MAX).into()));
        assert!(factors.contains(&format!("{}^6-1", NumericFactor::MAX).into()));
        assert!(factors.contains(&format!("{}^4+1", NumericFactor::MAX).into()));
        assert!(factors.contains(&format!("{}^4-1", NumericFactor::MAX).into()));
        assert!(factors.contains(&format!("{}^3+1", NumericFactor::MAX).into()));
        assert!(factors.contains(&format!("{}^3-1", NumericFactor::MAX).into()));
        assert!(factors.contains(&format!("{}^2+1", NumericFactor::MAX).into()));
        assert!(factors.contains(&format!("{}^2-1", NumericFactor::MAX).into()));
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

        assert_eq!(evaluate_as_numeric(&expr), Some(1 << 81));
    }

    #[test]
    fn test_division_associativity() {
        let expr = "20/5/2".into();

        assert_eq!(evaluate_as_numeric(&expr), Some(2));
    }

    #[test]
    fn test_stack_depth() {
        // unsafe { backtrace_on_stack_overflow::enable() };
        let expr = repeat_n("(2^9+1)", 1 << 16).join("*");
        find_factors(&expr);
        let expr = Arc::new(Factor::from(expr));
        crate::algebraic::estimate_log10_internal(Arc::clone(&expr));
        evaluate_as_numeric(&expr);
    }

    #[test]
    fn test_stack_depth_2() {
        const PRIMORIAL: NumericFactor = 2 * 3 * 5 * 7 * 11 * 13 * 17 * 19;
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
        assert_eq!(evaluate_as_numeric(&"2##".into()), Some(6)); // 2## = 6; (2#)# = 2
        assert_eq!(evaluate_as_numeric(&"2###".into()), Some(30)); // 2### = (2##)# = 30; (2#)## = 6

        // 2#### = (2##)## = 30030
        assert_eq!(evaluate_as_numeric(&"2####".into()), Some(30030));
        // (3#)### = 30029#
        // (3##)## = 113#
        // (3###)# = 6469693230#

        println!("{}", find_factors("92##".into()).into_iter().join(","));
    }

    #[test]
    fn test_m_precedence() {
        assert_eq!(evaluate_as_numeric(&"M7^2".into()), Some(127 * 127));
        assert_eq!(evaluate_as_numeric(&"M7*5".into()), Some(127 * 5));
        assert_eq!(evaluate_as_numeric(&"M5!".into()), Some((1..=31).product())); // (M5)!
        assert_eq!(
            evaluate_as_numeric(&"M5#".into()),
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
        unique_factors.sort_unstable();
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
        unique_larger_factors.sort_unstable();
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
        fn estimate_log10_internal(input: &str) -> (NumberLength, NumberLength) {
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
        let (lower, upper) =
            estimate_log10_internal(&("1".to_string() + &repeat_n('0', 50).collect::<String>()));
        assert_eq!(lower, 50);
        assert!(upper == 50 || upper == 51);
        let (lower, upper) = estimate_log10_internal(&(repeat_n('9', 50).collect::<String>()));
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
    fn test_evaluate_as_numeric() {
        assert_eq!(
            evaluate_as_numeric(&"2^127-1".into()),
            Some(i128::MAX as NumericFactor)
        );
        assert_eq!(evaluate_as_numeric(&"(5^6+1)^2-1".into()), Some(244171875));
        assert_eq!(evaluate_as_numeric(&"3^3+4^4+5^5".into()), Some(3408));
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
        assert!(!may_be_proper_divisor_of(
            "2/1234512345123451234512345123451234512345",
            "1234512345123451234512345123451234512345"
        ));
        assert!(!may_be_proper_divisor_of(
            "1234512345123451234512345123451234512345/2",
            "1234512345123451234512345123451234512345"
        ));
        assert!(!may_be_proper_divisor_of("2^1234-1", "(2^1234-1)/3"));
    }
    #[test]
    fn test_find_factors_performance() {
        use num_prime::detail::SMALL_PRIMES;
        println!("SMALL_PRIMES length: {}", SMALL_PRIMES.len());
        let start = std::time::Instant::now();
        // 10^111+1
        let expr = super::expression_parser::arithmetic("10^111+1").unwrap();
        let factors = super::find_factors(expr.into());
        println!("Time: {:?}", start.elapsed());
        // Verify we found something useful
        println!("Factors count: {}", factors.len());
        let expr = super::expression_parser::arithmetic("((12527^1075-1)/(12527^215-1)/8586556973449927230597763048446094420249471522535704574960623985727884084794871403158551-1)/1804837429895850").unwrap();
        let factors = super::find_factors(expr.into());
        println!("Time: {:?}", start.elapsed());
        // Verify we found something useful
        println!("Factors count: {}", factors.len());
    }

    #[test]
    fn test_factor_big_num_symbolic() {
        // "1212...12" (50 times)
        // Sum = (1+2)*50 = 150 (div by 3). Ends in 2 (div by 2).
        let repeated_12 = "12".repeat(50);
        let expr = super::expression_parser::arithmetic(&repeated_12).unwrap();
        let factors = super::find_factors(expr.into());

        // Should contain 2 and 3.
        assert!(factors.contains(&Factor::two()));
        assert!(factors.contains(&Factor::three()));

        // Should contain a generic factor which is the Divide term
        let has_divide = factors.iter().any(|f| matches!(**f, Factor::Divide { ref right, .. } if right.contains_key(&Factor::two())));
        assert!(has_divide, "Should return a symbolic Divide term");

        // Should prevent infinite recursion
        factors.into_iter().for_each(|f| {
            super::find_factors(f);
        });
    }

    #[test]
    fn test_large_fibonacci_lucas_factors() {
        use primitive_types::U256;
        fn fib(n: usize) -> U256 {
            let mut a = U256::from(0);
            let mut b = U256::from(1);
            for _ in 0..n {
                let tmp = a;
                a = b;
                b = tmp + b;
            }
            a
        }

        fn luc(n: usize) -> U256 {
            let mut a = U256::from(2);
            let mut b = U256::from(1);
            for _ in 0..n {
                let tmp = a;
                a = b;
                b = tmp + b;
            }
            a
        }

        for n in 2..=300 {
            let f_n = fib(n);
            let factors = fibonacci_factors(n as NumericFactor, true);
            let mut product = U256::from(1);
            for factor in factors {
                if let Some(val) = evaluate_as_numeric(&factor) {
                    assert_eq!(
                        f_n % U256::from(val),
                        U256::from(0),
                        "Factor {} of F({}) = {} is not a divisor",
                        val,
                        n,
                        f_n
                    );
                    product *= U256::from(val);
                } else {
                    assert!(
                        n >= SMALL_FIBONACCI_FACTORS.len(),
                        "Factor {:?} of I({}) is not numeric",
                        factor,
                        n
                    );
                }
            }
            if n < SMALL_FIBONACCI_FACTORS.len() {
                assert_eq!(product, f_n, "Product of factors of F({}) != I({})", n, n);
            } else {
                assert!(product <= f_n);
            }

            let l_n = luc(n);
            let factors = lucas_factors(n as NumericFactor, true);
            let mut product = U256::from(1);
            for factor in factors {
                if let Some(val) = evaluate_as_numeric(&factor) {
                    assert_eq!(
                        l_n % U256::from(val),
                        U256::from(0),
                        "Factor {} of L({}) = {} is not a divisor",
                        val,
                        n,
                        l_n
                    );
                    product *= U256::from(val);
                } else {
                    assert!(
                        n >= SMALL_LUCAS_FACTORS.len(),
                        "Factor {:?} of L({}) is not numeric",
                        factor,
                        n
                    );
                }
            }
            if n < SMALL_LUCAS_FACTORS.len() {
                assert_eq!(product, l_n, "Product of factors of L({}) != L({})", n, n);
            } else {
                assert!(product <= l_n);
            }
        }
    }

    #[test]
    fn test_parse_elided() {
        assert!(matches!(Factor::from("2002...96"), Factor::ElidedNumber(_)));
    }
}
