use crate::algebraic::Factor::Numeric;
use crate::algebraic::NumberStatus::{
    FullyFactored, PartlyFactoredComposite, UnfactoredComposite, Unknown,
};
use crate::net::ThrottlingHttpClient;
use crate::{
    MAX_ID_EQUAL_TO_VALUE, NumberSpecifier, NumberStatusApiResponse, RETRY_DELAY, write_bignum,
};
use async_backtrace::framed;
use compact_str::{CompactString, ToCompactString, format_compact};
use itertools::Itertools;
use log::{error, info, warn};
use num_integer::Integer;
use num_modular::{ModularCoreOps, ModularPow};
use num_prime::ExactRoots;
use num_prime::Primality::No;
use num_prime::buffer::{NaiveBuffer, PrimeBufferExt};
use num_prime::nt_funcs::factorize128;
use regex::{Regex, RegexBuilder, RegexSet};
use serde_json::from_str;
use std::borrow::Cow::{Borrowed, Owned};
use std::borrow::{Borrow, Cow};
use std::cmp::{Ordering, PartialEq};
use std::collections::BTreeMap;
use std::fmt::{Display, Formatter};
use std::hash::{Hash, Hasher};
use std::hint::unreachable_unchecked;
use std::iter::repeat_n;
use std::marker::Destruct;
use std::mem::swap;
use std::sync::Arc;
use urlencoding::encode;

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

#[derive(Copy, Clone, Debug)]
pub enum Factor<T, U> {
    Numeric(u128),
    BigNumber(T),
    Expression(U),
}

impl<T: AsRef<str>, U: AsRef<str>> Hash for Factor<T, U> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        match self {
            Numeric(n) => n.hash(state),
            Factor::BigNumber(n) => n.as_ref().hash(state),
            Factor::Expression(e) => e.as_ref().hash(state),
        }
    }
}

impl<T, U> From<u128> for Factor<T, U> {
    #[inline(always)]
    fn from(value: u128) -> Self {
        Numeric(value)
    }
}

macro_rules! factor_from {
    ($input:ty, $output_bignum:ty, $output_expression:ty) => {
        impl From<$input> for Factor<$output_bignum, $output_expression> {
            #[inline(always)]
            fn from(value: $input) -> Self {
                match value.parse() {
                    Ok(n) => Numeric(n),
                    Err(_) => {
                        if value.as_str().chars().all(|c| c.is_ascii_digit()) {
                            Factor::BigNumber(value.into())
                        } else {
                            Factor::Expression(value.into())
                        }
                    }
                }
            }
        }
    };
}

factor_from!(String, Arc<str>, CompactString);
factor_from!(CompactString, Arc<str>, CompactString);
factor_from!(&str, Arc<str>, CompactString);

impl<'a> From<&'a str> for Factor<&'a str, &'a str> {
    #[inline(always)]
    fn from(value: &'a str) -> Self {
        match value.parse() {
            Ok(n) => Numeric(n),
            Err(_) => {
                if value.as_str().chars().all(|c| c.is_ascii_digit()) {
                    Factor::BigNumber(value)
                } else {
                    Factor::Expression(value)
                }
            }
        }
    }
}

impl<T: Display, U: Display> From<Factor<T, U>> for CompactString {
    fn from(val: Factor<T, U>) -> Self {
        match val {
            Numeric(n) => n.to_compact_string(),
            Factor::BigNumber(n) => n.to_compact_string(),
            Factor::Expression(e) => e.to_compact_string(),
        }
    }
}

impl<'a, T, U> From<&'a Factor<T, U>> for Factor<&'a str, &'a str>
where
    &'a str: From<&'a T> + From<&'a U>,
{
    fn from(value: &'a Factor<T, U>) -> Self {
        match value {
            Numeric(n) => Numeric(*n),
            Factor::BigNumber(s) => Factor::BigNumber(s.into()),
            Factor::Expression(s) => Factor::Expression(s.into()),
        }
    }
}

impl<'a, T: Display, U: Display> From<&'a Factor<T, U>> for Factor<Arc<str>, CompactString> {
    fn from(value: &'a Factor<T, U>) -> Self {
        match value {
            Numeric(n) => Numeric(*n),
            Factor::Expression(s) => Factor::Expression(s.to_compact_string()),
            Factor::BigNumber(s) => Factor::BigNumber(s.to_string().into()),
        }
    }
}

impl<T: AsRef<str>, U: Display> Display for Factor<T, U> {
    #[inline(always)]
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Numeric(n) => n.fmt(f),
            Factor::Expression(s) => s.fmt(f),
            Factor::BigNumber(s) => write_bignum(f, s.as_ref()),
        }
    }
}

impl<T: AsRef<str>, U: AsRef<str>, V: AsRef<str>, W: AsRef<str>> PartialEq<Factor<T, U>>
    for Factor<V, W>
{
    fn eq(&self, other: &Factor<T, U>) -> bool {
        match self {
            Numeric(n) => {
                if let Numeric(o) = other
                    && n == o
                {
                    true
                } else {
                    false
                }
            }
            Factor::Expression(s) => {
                if let Factor::Expression(o) = other
                    && s.as_ref() == o.as_ref()
                {
                    true
                } else {
                    false
                }
            }
            Factor::BigNumber(s) => {
                if let Factor::BigNumber(o) = other
                    && s.as_ref() == o.as_ref()
                {
                    true
                } else {
                    false
                }
            }
        }
    }
}

impl<T: AsRef<str>, U: AsRef<str>> Eq for Factor<T, U> {}

impl<T: AsRef<str>, U: AsRef<str>, V: AsRef<str>, W: AsRef<str>> PartialOrd<Factor<V, W>>
    for Factor<T, U>
{
    #[inline(always)]
    fn partial_cmp(&self, other: &Factor<V, W>) -> Option<Ordering> {
        Some(match self {
            Numeric(n) => match other {
                Numeric(o) => n.cmp(o),
                Factor::Expression(_) => Ordering::Less,
                Factor::BigNumber(_) => Ordering::Less,
            },
            Factor::Expression(s) => match other {
                Numeric(_) => Ordering::Greater,
                Factor::BigNumber(_) => Ordering::Greater,
                Factor::Expression(o) => s
                    .as_ref()
                    .len()
                    .cmp(&o.as_ref().len())
                    .then_with(|| s.as_ref().cmp(o.as_ref())),
            },
            Factor::BigNumber(s) => match other {
                Numeric(_) => Ordering::Greater,
                Factor::Expression(_) => Ordering::Less,
                Factor::BigNumber(o) => s
                    .as_ref()
                    .len()
                    .cmp(&o.as_ref().len())
                    .then_with(|| s.as_ref().cmp(o.as_ref())),
            },
        })
    }
}

impl<T: AsRef<str>, U: AsRef<str>> Ord for Factor<T, U> {
    #[inline(always)]
    fn cmp(&self, other: &Self) -> Ordering {
        self.partial_cmp(other).unwrap()
    }
}

impl<T: AsRef<str>, U: AsRef<str>> Factor<T, U> {
    pub fn as_str(&self) -> Cow<'_, str> {
        match self {
            Numeric(n) => Owned(n.to_string()),
            Factor::BigNumber(s) => Borrowed(s.as_ref()),
            Factor::Expression(s) => Borrowed(s.as_ref()),
        }
    }

    pub fn as_str_non_u128(&self) -> Option<&str> {
        match self {
            Numeric(_) => None,
            Factor::BigNumber(n) => Some(n.as_ref()),
            Factor::Expression(s) => Some(s.as_ref()),
        }
    }

    pub fn as_ref(&self) -> Factor<&str, &str> {
        match self {
            Numeric(n) => Numeric(*n),
            Factor::BigNumber(s) => Factor::BigNumber(s.as_ref()),
            Factor::Expression(s) => Factor::Expression(s.as_ref()),
        }
    }

    pub fn unambiguously_less_or_equal(&self, other: &Factor<T, U>) -> bool {
        if let Factor::Expression(_) = self {
            self == other
        } else if let Factor::Expression(_) = other {
            self == other
        } else {
            self.cmp(other) != Ordering::Greater
        }
    }
}

impl<T, U> Factor<T, U> {
    pub fn as_u128(&self) -> Option<u128> {
        match self {
            Numeric(n) => Some(*n),
            Factor::Expression(_) => None,
            Factor::BigNumber(_) => None,
        }
    }
}

#[inline(always)]
fn checked_product_u128<T, U, V: Borrow<Factor<T, U>>>(factors: &[V]) -> Option<u128> {
    let mut product = 1u128;
    for factor in factors {
        if let Numeric(n) = factor.borrow()
            && let Some(times_n) = product.checked_mul(*n)
        {
            product = times_n;
        } else {
            return None;
        }
    }
    Some(product)
}

pub enum SignedFactor<T, U> {
    Positive(Factor<T, U>),
    Zero,
    Negative(Factor<T, U>),
}

impl<T, U> SignedFactor<T, U> {
    #[inline(always)]
    fn abs(&self) -> &Factor<T, U> {
        match self {
            SignedFactor::Positive(f) => f,
            SignedFactor::Negative(f) => f,
            SignedFactor::Zero => &Numeric(0),
        }
    }
}

impl<'a> From<&'a str> for SignedFactor<&'a str, &'a str> {
    #[inline(always)]
    fn from(value: &'a str) -> Self {
        if let Some(negated) = value.strip_prefix('-') {
            SignedFactor::Negative(negated.into())
        } else if value == "0" {
            SignedFactor::Zero
        } else {
            SignedFactor::Positive(value.into())
        }
    }
}

pub struct FactorFinder {
    regexes: Box<[Regex]>,
    regexes_as_set: RegexSet,
    sieve: NaiveBuffer,
    digits_fallback_regex: Regex,
}

impl Clone for FactorFinder {
    #[inline(always)]
    fn clone(&self) -> Self {
        FactorFinder {
            regexes: self.regexes.clone(),
            regexes_as_set: self.regexes_as_set.clone(),
            sieve: NaiveBuffer::new(),
            digits_fallback_regex: self.digits_fallback_regex.clone(),
        }
    }

    #[inline(always)]
    fn clone_from(&mut self, _source: &Self)
    where
        Self: Destruct,
    {
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
fn multiset_union<T: Eq + Ord + Clone, U: Ord + From<T> + Clone>(
    vec1: Vec<T>,
    vec2: Vec<U>,
) -> Vec<U> {
    if vec1.is_empty() {
        return vec2;
    }
    if vec2.is_empty() {
        return vec1.into_iter().map(|item| item.into()).collect();
    }
    let counts1 = count_frequencies(vec1);
    let mut counts2 = count_frequencies(vec2);
    for (item, count1) in counts1.into_iter() {
        let union_count = counts2.entry(item.into()).or_insert(0);
        *union_count = (*union_count).max(count1);
    }
    counts2
        .into_iter()
        .flat_map(|(item, count)| repeat_n(item, count))
        .collect()
}

#[inline(always)]
fn multiset_difference<T: Eq + Ord + Clone, U: Eq + Ord + From<T>, V: From<T> + Clone>(
    vec1: Vec<T>,
    vec2: &[U],
) -> Vec<V> {
    if vec2.is_empty() {
        return vec1.into_iter().map(|item| item.into()).collect();
    }
    if vec1.is_empty() {
        return vec![];
    }
    let mut difference_vec = Vec::with_capacity(vec1.len());
    let counts1 = count_frequencies(vec1);
    let counts2 = count_frequencies_ref(vec2);

    for (item, mut count) in counts1 {
        if let Some(&count2) = counts2.get::<U>(&item.clone().into()) {
            count = count.saturating_sub(count2);
        }
        difference_vec.extend(repeat_n(item.into(), count));
    }
    difference_vec
}

#[inline]
fn fibonacci_factors(term: u128, subset_recursion: bool) -> Vec<Factor<Arc<str>, CompactString>> {
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
        [format_compact!("I({})", term).into()].into()
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
fn lucas_factors(term: u128, subset_recursion: bool) -> Vec<Factor<Arc<str>, CompactString>> {
    if term < SMALL_LUCAS_FACTORS.len() as u128 {
        SMALL_LUCAS_FACTORS[term as usize]
            .iter()
            .copied()
            .map(Factor::from)
            .collect()
    } else if !subset_recursion {
        [format_compact!("lucas({})", term).into()].into()
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

impl FactorFinder {
    #[inline(always)]
    pub fn new() -> FactorFinder {
        let regexes_as_set = RegexSet::new([
            "^lucas\\(([0-9]+)\\)$",
            "^I\\(([0-9]+)\\)$",
            "^([0-9]+)\\^([0-9]+)(\\*[0-9]+)?([+-][0-9]+)?$",
            "^([0-9]+!)$",
            "^([0-9]+#)$",
            "^([0-9]+)$",
            "^([0-9]+\\.\\.+[0-9]+)$",
            "^\\(([^()]+)\\)$",
            "^([^+-]+|\\([^()]+\\))/([^+-]+|\\([^()]+\\))$",
            "^([^+-]+|\\([^()]+\\))\\*([^+-]+|\\([^()]+\\))$",
            "^([^()]+|\\([^()]+\\))[+-]([^()]+|\\([^()]+\\))$",
        ])
        .unwrap();
        let regexes = regexes_as_set
            .patterns()
            .iter()
            .map(|pat| Regex::new(pat).unwrap())
            .collect();
        let sieve = NaiveBuffer::new();
        let digits_fallback_regex =
            RegexBuilder::new("<tr><td>Number</td>[^<]*<td[^>]*>([0-9br<>\\pZ]+)")
                .multi_line(true)
                .dot_matches_new_line(true)
                .build()
                .unwrap();
        FactorFinder {
            regexes,
            regexes_as_set,
            sieve,
            digits_fallback_regex,
        }
    }

    #[inline]
    fn find_factors_of_u128<T: Clone, U: Clone>(input: u128) -> Vec<Factor<T, U>> {
        factorize128(input)
            .into_iter()
            .flat_map(|(factor, power)| repeat_n(Numeric(factor), power))
            .collect()
    }

    #[inline]
    fn find_factors<T: AsRef<str>, U: AsRef<str> + Display>(
        &self,
        expr: &Factor<T, U>,
    ) -> Vec<Factor<Arc<str>, CompactString>> {
        match expr {
            Numeric(n) => Self::find_factors_of_u128(*n),
            Factor::BigNumber(expr) => Self::factor_big_num(expr),
            Factor::Expression(expr) => {
                if let Some(index) = self
                    .regexes_as_set
                    .matches(expr.as_ref())
                    .into_iter()
                    .next()
                {
                    let captures = self.regexes[index].captures(expr.as_ref()).unwrap();
                    match index {
                        0 => {
                            // Lucas number
                            let Ok(term_number) = captures[1].parse::<u128>() else {
                                warn!(
                                    "Could not parse term number of a Lucas number: {}",
                                    &captures[1]
                                );
                                return vec![expr.to_compact_string().into()];
                            };
                            lucas_factors(term_number, true)
                        }
                        1 => {
                            // Fibonacci number
                            let Ok(term_number) = captures[1].parse::<u128>() else {
                                warn!(
                                    "Could not parse term number of a Fibonacci number: {}",
                                    &captures[1]
                                );
                                return vec![expr.to_compact_string().into()];
                            };
                            fibonacci_factors(term_number, true)
                        }
                        2 => {
                            // a^n*b + c
                            let mut factors = Vec::new();
                            let a = Factor::from(&captures[1]);
                            let mut b = Numeric(1u128);
                            if let Some(b_match) = captures.get(3) {
                                b = Factor::from(&b_match.as_str()[1..]);
                            }
                            let c_raw = if let Some(c_match) = captures.get(4) {
                                SignedFactor::from(c_match.as_str())
                            } else {
                                let n = captures[2].parse::<u128>().unwrap_or(16).min(16) as usize;
                                factors.extend(repeat_n(self.find_factors(&a), n).flatten());
                                factors.extend(self.find_factors(&b));
                                return factors;
                            };
                            let gcd_bc = self.find_common_factors(&b, c_raw.abs(), false);
                            let b = self.find_factors(&b);
                            let c_abs = self.find_factors(c_raw.abs());
                            let gcd_ac = self.find_common_factors(&a, c_raw.abs(), false);
                            let n: Factor<&str, &str> = Factor::from(&captures[2]);
                            if let Numeric(a) = a
                                && let Numeric(n) = n
                            {
                                let b_reduced: Vec<Factor<Arc<str>, CompactString>> =
                                    multiset_difference(b, &gcd_bc);
                                let c_reduced: Vec<Factor<Arc<str>, CompactString>> =
                                    multiset_difference(c_abs, &gcd_bc);
                                factors.extend(multiset_union(gcd_ac, gcd_bc));
                                if let Some(b) = checked_product_u128(b_reduced.as_slice())
                                    && let Some(abs_c) = checked_product_u128(c_reduced.as_slice())
                                {
                                    let anb_u128 = n
                                        .try_into()
                                        .ok()
                                        .and_then(|n| a.checked_pow(n))
                                        .and_then(|an| an.checked_mul(b));
                                    let (c, anbc_u128) = if let SignedFactor::Negative(_) = c_raw {
                                        (
                                            0i128.checked_sub_unsigned(abs_c),
                                            anb_u128.and_then(|anb| anb.checked_sub(abs_c)),
                                        )
                                    } else {
                                        (
                                            0i128.checked_add_unsigned(abs_c),
                                            anb_u128.and_then(|anb| anb.checked_add(abs_c)),
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
                                    let factors_of_n = Self::find_factors_of_u128(n);
                                    let factors_of_n_count = factors_of_n.len();
                                    let mut factors_of_n = factors_of_n
                                        .iter()
                                        .collect::<Vec<&Factor<Arc<str>, CompactString>>>();
                                    for factor_subset in power_multiset(&mut factors_of_n) {
                                        if factor_subset.len() == factors_of_n_count
                                            || factor_subset.is_empty()
                                        {
                                            continue;
                                        }
                                        let Some(subset_product) =
                                            checked_product_u128(factor_subset.as_slice())
                                        else {
                                            continue;
                                        };
                                        if (a.powm(n, &subset_product).mulm(b, &subset_product)
                                            as i128
                                            + c)
                                            % (subset_product as i128)
                                            == 0
                                        {
                                            factors
                                                .extend(Self::find_factors_of_u128(subset_product));
                                        }
                                        if c > 0 && (n / subset_product).is_multiple_of(2) {
                                            continue;
                                        }
                                        if n % subset_product == 0
                                            && (c > 0 || !subset_product.is_multiple_of(2))
                                            && let Ok(prime_for_root) = subset_product.try_into()
                                            && let Some(root_c) = c.nth_root_exact(prime_for_root)
                                            && let Some(root_b) = b.nth_root_exact(prime_for_root)
                                        {
                                            if let Some(factor_u128) = a
                                                .checked_pow(prime_for_root)
                                                .and_then(|an| an.checked_mul(b))
                                                .and_then(|anb| anb.checked_add_signed(c))
                                            {
                                                factors.extend(Self::find_factors_of_u128(
                                                    factor_u128,
                                                ));
                                            } else {
                                                let factor_expr = format_compact!(
                                                    "{}{}{}{}",
                                                    a,
                                                    if n / subset_product > 1 {
                                                        format_compact!("^{}", n / subset_product)
                                                    } else {
                                                        CompactString::from("")
                                                    },
                                                    if root_b > 1 {
                                                        format_compact!("*{}", root_b)
                                                    } else {
                                                        CompactString::from("")
                                                    },
                                                    if root_c != 0 {
                                                        format_compact!("{:+}", root_c)
                                                    } else {
                                                        CompactString::from("")
                                                    }
                                                );
                                                factors.push(factor_expr.into());
                                            }
                                        }
                                    }
                                }
                            } else {
                                factors.extend(multiset_union(gcd_ac, gcd_bc));
                            }
                            factors
                        }
                        3 => {
                            // factorial
                            let Ok(input) = captures[1].parse::<u128>() else {
                                warn!(
                                    "Could not parse input to factorial function: {}",
                                    &captures[1]
                                );
                                return vec![expr.to_compact_string().into()];
                            };
                            let mut factors = Vec::new();
                            for i in 2..=input {
                                factors.extend(Self::find_factors_of_u128(i));
                            }
                            factors
                        }
                        4 => {
                            // primorial
                            let Ok(input) = captures[1].parse::<u128>() else {
                                warn!(
                                    "Could not parse input to primorial function: {}",
                                    &captures[1]
                                );
                                return vec![expr.to_compact_string().into()];
                            };
                            let mut factors = Vec::new();
                            for i in 2..=input {
                                if self.sieve.is_prime(&i, None) != No {
                                    factors.push(Numeric(i));
                                }
                            }
                            factors
                        }
                        5 => {
                            // Raw number
                            Self::factor_big_num(expr)
                        }
                        6 => {
                            // elided number
                            match expr.as_ref().chars().last() {
                                Some('0') => vec![Numeric(2), Numeric(5)],
                                Some('5') => vec![Numeric(5)],
                                Some('2' | '4' | '6' | '8') => vec![Numeric(5)],
                                Some('1' | '3' | '7' | '9') => vec![],
                                x => {
                                    error!("Invalid last digit: {x:?}");
                                    vec![]
                                }
                            }
                        }
                        7 => {
                            // parens
                            let inner_expr: Factor<&str, &str> = captures[1].into();
                            self.find_factors(&inner_expr)
                        }
                        8 => {
                            // division by another expression
                            let numerator: Factor<&str, &str> = captures[1].into();
                            let numerator = self.find_factors(&numerator);
                            let denominator: Factor<Arc<str>, CompactString> = captures[2].into();
                            let denominator = if numerator.contains(&denominator) {
                                vec![denominator]
                            } else {
                                self.find_factors(&denominator)
                            };
                            multiset_difference(numerator, &denominator)
                        }
                        9 => {
                            let mut factors = Vec::new();
                            // multiplication
                            for term in [captures[1].into(), captures[2].into()] {
                                let term_factors = self.find_factors(&term);
                                if term_factors.is_empty() {
                                    factors.push(term);
                                } else {
                                    factors.extend(term_factors);
                                }
                            }
                            factors
                        }
                        10 => {
                            // addition/subtraction; only return common factors of both sides, and 2
                            // if both are odd
                            let left_expr: Factor<&str, &str> = captures[1].into();
                            let right_expr: Factor<&str, &str> = captures[2].into();
                            self.find_common_factors(&left_expr, &right_expr, true)
                        }
                        _ => unsafe { unreachable_unchecked() },
                    }
                } else {
                    vec![expr.to_compact_string().into()]
                }
            }
        }
    }

    fn factor_big_num<T: AsRef<str>>(expr: &T) -> Vec<Factor<Arc<str>, CompactString>> {
        let mut factors = Vec::new();
        let mut expr_short = expr.as_ref();
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
    fn find_common_factors<T: AsRef<str> + Display, U: AsRef<str> + Display>(
        &self,
        expr1: &Factor<T, U>,
        expr2: &Factor<T, U>,
        for_add_or_sub: bool,
    ) -> Vec<Factor<Arc<str>, CompactString>> {
        if let Numeric(num1) = expr1
            && let Numeric(num2) = expr2
        {
            factorize128(num1.gcd(num2))
                .into_iter()
                .flat_map(|(factor, power)| repeat_n(Numeric(factor), power))
                .collect()
        } else {
            let expr1_factors = self.find_factors(expr1);
            let expr2_factors = self.find_factors(expr2);
            let both_odd = for_add_or_sub
                && !expr1_factors.contains(&Numeric(2))
                && !expr2_factors.contains(&Numeric(2));
            let mut results = multiset_intersection(expr1_factors, expr2_factors);
            if both_odd {
                results.push(Numeric(2));
            }
            results
        }
    }

    /// Returns all unique, nontrivial factors we can find.
    #[inline(always)]
    pub fn find_unique_factors<T: AsRef<str> + Display, U: AsRef<str> + Display>(
        &self,
        expr: &Factor<T, U>,
    ) -> Box<[Factor<Arc<str>, CompactString>]> {
        let mut factors = self.find_factors(expr);
        factors.retain(|f| match f {
            Numeric(n) => {
                *n > 1
                    && if let Numeric(expr) = expr {
                        *n <= *expr >> 1
                    } else {
                        true
                    }
            }
            Factor::Expression(s) => {
                f != expr
                    && if let Factor::Expression(expr) = &expr {
                        !expr.as_ref().starts_with(&format!("{s}/"))
                    } else {
                        true
                    }
            }
            Factor::BigNumber(_) => true,
        });
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

    // FIXME: This uses Web requests to find factors that FactorDB already knows of and/or convert
    // them to digit form. That would be out of scope for this struct if we had anywhere else to put
    // this method.
    #[framed]
    #[inline]
    pub async fn known_factors_as_digits<T: AsRef<str>, U: AsRef<str>>(
        &self,
        http: &ThrottlingHttpClient,
        id: NumberSpecifier<T, U>,
        include_ff: bool,
        get_digits_as_fallback: bool,
    ) -> ProcessedStatusApiResponse {
        if let NumberSpecifier::Expression(Numeric(n)) = id {
            return ProcessedStatusApiResponse {
                status: Some(FullyFactored),
                factors: Self::find_factors_of_u128(n).into_boxed_slice(),
                id: if n <= MAX_ID_EQUAL_TO_VALUE {
                    Some(n)
                } else {
                    None
                },
            };
        }
        if let NumberSpecifier::Id(id) = id
            && id <= MAX_ID_EQUAL_TO_VALUE
        {
            return ProcessedStatusApiResponse {
                status: Some(FullyFactored),
                factors: Self::find_factors_of_u128(id).into_boxed_slice(),
                id: Some(id),
            };
        }
        let response = match id {
            NumberSpecifier::Id(id) => {
                let url = format!("https://factordb.com/api?id={id}");
                if get_digits_as_fallback {
                    http.retrying_get_and_decode_or(&url, RETRY_DELAY, || {
                        format!("https://factordb.com/index.php?showid={id}")
                    })
                    .await
                    .map_err(Some)
                } else {
                    http.try_get_and_decode(&url).await.ok_or(None)
                }
            }
            NumberSpecifier::Expression(ref expr) => {
                let url = format!("https://factordb.com/api?query={}", encode(&expr.as_str()));
                http.try_get_and_decode(&url).await.ok_or(None)
            }
        };
        match response {
            Ok(api_response) => match from_str::<NumberStatusApiResponse>(&api_response) {
                Err(e) => {
                    error!("{id}: Failed to decode API response: {e}: {api_response}");
                    ProcessedStatusApiResponse::default()
                }
                Ok(NumberStatusApiResponse {
                    status,
                    factors,
                    id: recvd_id,
                }) => {
                    info!(
                        "{id}: Fetched status of {status} and {} factors of sizes {}",
                        factors.len(),
                        factors.iter().map(|(digits, _)| digits.len()).join(",")
                    );
                    let recvd_id = recvd_id.to_string().parse::<u128>().ok();
                    let status = match status.as_str() {
                        "FF" | "P" | "PRP" => Some(FullyFactored),
                        "C" => Some(UnfactoredComposite),
                        "CF" => Some(PartlyFactoredComposite),
                        "U" => Some(Unknown),
                        x => {
                            error!("{recvd_id:?} ({id}): Unrecognized number status code: {x}");
                            None
                        }
                    };
                    let factors = if !include_ff && status == Some(FullyFactored) {
                        Box::new([])
                    } else {
                        let mut factors: Vec<_> = factors
                            .into_iter()
                            .map(|(factor, _exponent)| Factor::from(factor))
                            .collect();
                        factors.sort();
                        factors.dedup();
                        factors.into_boxed_slice()
                    };
                    ProcessedStatusApiResponse {
                        status,
                        factors,
                        id: recvd_id,
                    }
                }
            },
            Err(None) => ProcessedStatusApiResponse {
                status: None,
                id: None,
                factors: Box::new([]),
            },
            Err(Some(fallback_response)) => {
                let factors = self
                    .digits_fallback_regex
                    .captures(&fallback_response)
                    .and_then(|c| c.get(1))
                    .map(|digits_cell| {
                        vec![
                            digits_cell
                                .as_str()
                                .chars()
                                .filter(char::is_ascii_digit)
                                .collect::<CompactString>()
                                .into(),
                        ]
                        .into_boxed_slice()
                    })
                    .unwrap_or_else(|| Box::new([]));
                ProcessedStatusApiResponse {
                    status: None,
                    factors,
                    id: None,
                }
            }
        }
    }
}

#[derive(Default, Debug)]
pub struct ProcessedStatusApiResponse {
    pub status: Option<NumberStatus>,
    pub factors: Box<[Factor<Arc<str>, CompactString>]>,
    pub id: Option<u128>,
}

#[derive(Eq, PartialEq, Copy, Clone, Debug)]
pub enum NumberStatus {
    Unknown,
    FullyFactored, // includes P and PRP
    PartlyFactoredComposite,
    UnfactoredComposite,
}

#[cfg(test)]
mod tests {
    use crate::algebraic::Factor::Numeric;
    use crate::algebraic::{
        FactorFinder, SMALL_FIBONACCI_FACTORS, SMALL_LUCAS_FACTORS, fibonacci_factors,
        lucas_factors, multiset_difference, multiset_intersection, multiset_union, power_multiset,
    };
    use compact_str::{ToCompactString, format_compact};
    use itertools::Itertools;

    #[test]
    fn test_anbc() {
        let finder = FactorFinder::new();
        let expr = format_compact!("{}^9*3+3", u128::MAX);
        let factors = finder.find_factors(&expr.into());
        println!("{}", factors.iter().join(", "));
        assert!(factors.contains(&3.into()));
        assert!(factors.contains(&format_compact!("{}^3+1", u128::MAX).into()));
    }

    #[test]
    fn test_anbc_2() {
        let finder = FactorFinder::new();
        let factors = finder.find_factors(&"6^200600+1".to_compact_string().into());
        println!("{}", factors.iter().join(", "));

        // Should contain 6^8+1
        assert!(factors.contains(&17.into()));
        assert!(factors.contains(&98801.into()));

        // Shouldn't contain 6^5+1
        assert!(!factors.contains(&7.into()));
        assert!(!factors.contains(&11.into()));
        assert!(!factors.contains(&101.into()));
    }

    #[test]
    fn test_anb_minus_c() {
        let finder = FactorFinder::new();
        let expr = format_compact!("{}^24-1", u128::MAX);
        let factors = finder.find_factors(&expr.into());
        println!("{}", factors.iter().join(", "));
        assert!(factors.contains(&format_compact!("{}^8-1", u128::MAX).into()));
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
        let difference: Vec<i32> = multiset_difference(multiset_1, &multiset_2);
        assert_eq!(difference, vec![2, 7]);
    }
}
