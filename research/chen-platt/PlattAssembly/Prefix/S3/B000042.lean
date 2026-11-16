import PlattAssemblyKernel
import PlattCertificates.Count131072.C021344
import PlattCertificates.Count131072.C021345
import PlattCertificates.Count131072.C021346
import PlattCertificates.Count131072.C021347
import PlattCertificates.Count131072.C021348
import PlattCertificates.Count131072.C021349
import PlattCertificates.Count131072.C021350
import PlattCertificates.Count131072.C021351
import PlattCertificates.Count131072.C021352
import PlattCertificates.Count131072.C021353
import PlattCertificates.Count131072.C021354
import PlattCertificates.Count131072.C021355
import PlattCertificates.Count131072.C021356
import PlattCertificates.Count131072.C021357
import PlattCertificates.Count131072.C021358
import PlattCertificates.Count131072.C021359
import PlattCertificates.Count131072.C021360
import PlattCertificates.Count131072.C021361
import PlattCertificates.Count131072.C021362
import PlattCertificates.Count131072.C021363
import PlattCertificates.Count131072.C021364
import PlattCertificates.Count131072.C021365
import PlattCertificates.Count131072.C021366
import PlattCertificates.Count131072.C021367
import PlattCertificates.Count131072.C021368
import PlattCertificates.Count131072.C021369
import PlattCertificates.Count131072.C021370
import PlattCertificates.Count131072.C021371
import PlattCertificates.Count131072.C021372
import PlattCertificates.Count131072.C021373
import PlattCertificates.Count131072.C021374
import PlattCertificates.Count131072.C021375
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000042
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts21344 : List PrefixCut := [⟨58,271672677,271672834⟩,
⟨128,602112995,602113345⟩]
theorem checked21344 : checkPrefixCuts (2^48) 2801532929 9 Manual.Count131072.C021344.packed 128 cuts21344 = true := by
 decide +kernel
def pointBounds21344 : List (Nat × Nat × Nat) := [(2801592320,100862617319103,100862998178887)]
theorem point_links_checked21344 : (cuts21344.take 1).map (fun c => (2801532929-1+2*2^9*c.k,100862345646426+c.lower,100862726506053+c.upper)) = pointBounds21344 := by
 decide +kernel
def cuts21345 : List PrefixCut := [⟨16,79167797,79167841⟩,
⟨102,483739922,483740204⟩,
⟨128,608615215,608615568⟩]
theorem checked21345 : checkPrefixCuts (2^48) 2801664001 9 Manual.Count131072.C021345.packed 128 cuts21345 = true := by
 decide +kernel
def pointBounds21345 : List (Nat × Nat × Nat) := [(2801680384,100863026927218,100863407787239),(2801768448,100863431499343,100863812359602)]
theorem point_links_checked21345 : (cuts21345.take 2).map (fun c => (2801664001-1+2*2^9*c.k,100862947759421+c.lower,100863328619398+c.upper)) = pointBounds21345 := by
 decide +kernel
def cuts21346 : List PrefixCut := [⟨60,286716416,286716577⟩,
⟨128,605874344,605874691⟩]
theorem checked21346 : checkPrefixCuts (2^48) 2801795073 9 Manual.Count131072.C021346.packed 128 cuts21346 = true := by
 decide +kernel
def pointBounds21346 : List (Nat × Nat × Nat) := [(2801856512,100863843091052,100864223951543)]
theorem point_links_checked21346 : (cuts21346.take 1).map (fun c => (2801795073-1+2*2^9*c.k,100863556374636+c.lower,100863937234966+c.upper)) = pointBounds21346 := by
 decide +kernel
def cuts21347 : List PrefixCut := [⟨18,84283691,84283739⟩,
⟨104,491831235,491831509⟩,
⟨128,604238578,604238917⟩]
theorem checked21347 : checkPrefixCuts (2^48) 2801926145 9 Manual.Count131072.C021347.packed 128 cuts21347 = true := by
 decide +kernel
def pointBounds21347 : List (Nat × Nat × Nat) := [(2801944576,100864246532671,100864627393396),(2802032640,100864654080215,100865034941166)]
theorem point_links_checked21347 : (cuts21347.take 2).map (fun c => (2801926145-1+2*2^9*c.k,100864162248980+c.lower,100864543109657+c.upper)) = pointBounds21347 := by
 decide +kernel
def cuts21348 : List PrefixCut := [⟨62,296232357,296232529⟩,
⟨128,607022996,607023347⟩]
theorem checked21348 : checkPrefixCuts (2^48) 2802057217 9 Manual.Count131072.C021348.packed 128 cuts21348 = true := by
 decide +kernel
def pointBounds21348 : List (Nat × Nat × Nat) := [(2802120704,100865062719915,100865443581103)]
theorem point_links_checked21348 : (cuts21348.take 1).map (fun c => (2802057217-1+2*2^9*c.k,100864766487558+c.lower,100865147348574+c.upper)) = pointBounds21348 := by
 decide +kernel
def cuts21349 : List PrefixCut := [⟨20,98539379,98539434⟩,
⟨106,506148936,506149229⟩,
⟨128,609907535,609907885⟩]
theorem checked21349 : checkPrefixCuts (2^48) 2802188289 9 Manual.Count131072.C021349.packed 128 cuts21349 = true := by
 decide +kernel
def pointBounds21349 : List (Nat × Nat × Nat) := [(2802208768,100865472049933,100865852911355),(2802296832,100865879659490,100866260521150)]
theorem point_links_checked21349 : (cuts21349.take 2).map (fun c => (2802188289-1+2*2^9*c.k,100865373510554+c.lower,100865754371921+c.upper)) = pointBounds21349 := by
 decide +kernel
def cuts21350 : List PrefixCut := [⟨64,302733339,302733508⟩,
⟨128,604756486,604756827⟩]
theorem checked21350 : checkPrefixCuts (2^48) 2802319361 9 Manual.Count131072.C021350.packed 128 cuts21350 = true := by
 decide +kernel
def pointBounds21350 : List (Nat × Nat × Nat) := [(2802384896,100866286151428,100866667013314)]
theorem point_links_checked21350 : (cuts21350.take 1).map (fun c => (2802319361-1+2*2^9*c.k,100865983418089+c.lower,100866364279806+c.upper)) = pointBounds21350 := by
 decide +kernel
def cuts21351 : List PrefixCut := [⟨22,102949399,102949458⟩,
⟨108,514337166,514337454⟩,
⟨128,608544748,608545091⟩]
theorem checked21351 : checkPrefixCuts (2^48) 2802450433 9 Manual.Count131072.C021351.packed 128 cuts21351 = true := by
 decide +kernel
def pointBounds21351 : List (Nat × Nat × Nat) := [(2802472960,100866691123974,100867071986091),(2802561024,100867102511741,100867483374087)]
theorem point_links_checked21351 : (cuts21351.take 2).map (fun c => (2802450433-1+2*2^9*c.k,100866588174575+c.lower,100866969036633+c.upper)) = pointBounds21351 := by
 decide +kernel
def cuts21352 : List PrefixCut := [⟨66,317066771,317066950⟩,
⟨128,608616790,608617137⟩]
theorem checked21352 : checkPrefixCuts (2^48) 2802581505 9 Manual.Count131072.C021352.packed 128 cuts21352 = true := by
 decide +kernel
def pointBounds21352 : List (Nat × Nat × Nat) := [(2802649088,100867513786094,100867894648674)]
theorem point_links_checked21352 : (cuts21352.take 1).map (fun c => (2802581505-1+2*2^9*c.k,100867196719323+c.lower,100867577581724+c.upper)) = pointBounds21352 := by
 decide +kernel
def cuts21353 : List PrefixCut := [⟨24,112681355,112681422⟩,
⟨110,517904265,517904566⟩,
⟨128,603667296,603667643⟩]
theorem checked21353 : checkPrefixCuts (2^48) 2802712577 9 Manual.Count131072.C021353.packed 128 cuts21353 = true := by
 decide +kernel
def pointBounds21353 : List (Nat × Nat × Nat) := [(2802737152,100867918017468,100868298880283),(2802825216,100868323240378,100868704103427)]
theorem point_links_checked21353 : (cuts21353.take 2).map (fun c => (2802712577-1+2*2^9*c.k,100867805336113+c.lower,100868186198861+c.upper)) = pointBounds21353 := by
 decide +kernel
def cuts21354 : List PrefixCut := [⟨68,325974697,325974888⟩,
⟨128,609564062,609564411⟩]
theorem checked21354 : checkPrefixCuts (2^48) 2802843649 9 Manual.Count131072.C021354.packed 128 cuts21354 = true := by
 decide +kernel
def pointBounds21354 : List (Nat × Nat × Nat) := [(2802913280,100868734978106,100869115841392)]
theorem point_links_checked21354 : (cuts21354.take 1).map (fun c => (2802843649-1+2*2^9*c.k,100868409003409+c.lower,100868789866504+c.upper)) = pointBounds21354 := by
 decide +kernel
def cuts21355 : List PrefixCut := [⟨26,127532872,127532944⟩,
⟨112,530910090,530910398⟩,
⟨128,606422660,606423014⟩]
theorem checked21355 : checkPrefixCuts (2^48) 2802974721 9 Manual.Count131072.C021355.packed 128 cuts21355 = true := by
 decide +kernel
def pointBounds21355 : List (Nat × Nat × Nat) := [(2803001344,100869146100343,100869526963859),(2803089408,100869549477561,100869930341313)]
theorem point_links_checked21355 : (cuts21355.take 2).map (fun c => (2802974721-1+2*2^9*c.k,100869018567471+c.lower,100869399430915+c.upper)) = pointBounds21355 := by
 decide +kernel
def cuts21356 : List PrefixCut := [⟨70,330563168,330563353⟩,
⟨128,606896260,606896606⟩]
theorem checked21356 : checkPrefixCuts (2^48) 2803105793 9 Manual.Count131072.C021356.packed 128 cuts21356 = true := by
 decide +kernel
def pointBounds21356 : List (Nat × Nat × Nat) := [(2803177472,100869955553299,100870336417282)]
theorem point_links_checked21356 : (cuts21356.take 1).map (fun c => (2803105793-1+2*2^9*c.k,100869624990131+c.lower,100870005853929+c.upper)) = pointBounds21356 := by
 decide +kernel
def cuts21357 : List PrefixCut := [⟨28,133445119,133445195⟩,
⟨114,539997336,539997647⟩,
⟨128,608173165,608173514⟩]
theorem checked21357 : checkPrefixCuts (2^48) 2803236865 9 Manual.Count131072.C021357.packed 128 cuts21357 = true := by
 decide +kernel
def pointBounds21357 : List (Nat × Nat × Nat) := [(2803265536,100870365331510,100870746195730),(2803353600,100870771883727,100871152748182)]
theorem point_links_checked21357 : (cuts21357.take 2).map (fun c => (2803236865-1+2*2^9*c.k,100870231886391+c.lower,100870612750535+c.upper)) = pointBounds21357 := by
 decide +kernel
def cuts21358 : List PrefixCut := [⟨72,342279523,342279723⟩,
⟨128,612361724,612362082⟩]
theorem checked21358 : checkPrefixCuts (2^48) 2803367937 9 Manual.Count131072.C021358.packed 128 cuts21358 = true := by
 decide +kernel
def pointBounds21358 : List (Nat × Nat × Nat) := [(2803441664,100871182339079,100871563203772)]
theorem point_links_checked21358 : (cuts21358.take 1).map (fun c => (2803367937-1+2*2^9*c.k,100870840059556+c.lower,100871220924049+c.upper)) = pointBounds21358 := by
 decide +kernel
def cuts21359 : List PrefixCut := [⟨30,138954612,138954690⟩,
⟨116,540247851,540248161⟩,
⟨128,594662921,594663262⟩]
theorem checked21359 : checkPrefixCuts (2^48) 2803499009 9 Manual.Count131072.C021359.packed 128 cuts21359 = true := by
 decide +kernel
def pointBounds21359 : List (Nat × Nat × Nat) := [(2803529728,100871591375892,100871972240821),(2803617792,100871992669131,100872373534292)]
theorem point_links_checked21359 : (cuts21359.take 2).map (fun c => (2803499009-1+2*2^9*c.k,100871452421280+c.lower,100871833286131+c.upper)) = pointBounds21359 := by
 decide +kernel
def cuts21360 : List PrefixCut := [⟨74,345962011,345962213⟩,
⟨128,605578012,605578360⟩]
theorem checked21360 : checkPrefixCuts (2^48) 2803630081 9 Manual.Count131072.C021360.packed 128 cuts21360 = true := by
 decide +kernel
def pointBounds21360 : List (Nat × Nat × Nat) := [(2803705856,100872393046212,100872773911606)]
theorem point_links_checked21360 : (cuts21360.take 1).map (fun c => (2803630081-1+2*2^9*c.k,100872047084201+c.lower,100872427949393+c.upper)) = pointBounds21360 := by
 decide +kernel
def cuts21361 : List PrefixCut := [⟨32,152092843,152092928⟩,
⟨118,557062669,557062988⟩,
⟨128,604043968,604044313⟩]
theorem checked21361 : checkPrefixCuts (2^48) 2803761153 9 Manual.Count131072.C021361.packed 128 cuts21361 = true := by
 decide +kernel
def pointBounds21361 : List (Nat × Nat × Nat) := [(2803793920,100872804755056,100873185620681),(2803881984,100873209724882,100873590590741)]
theorem point_links_checked21361 : (cuts21361.take 2).map (fun c => (2803761153-1+2*2^9*c.k,100872652662213+c.lower,100873033527753+c.upper)) = pointBounds21361 := by
 decide +kernel
def cuts21362 : List PrefixCut := [⟨76,366307818,366308029⟩,
⟨128,607027343,607027695⟩]
theorem checked21362 : checkPrefixCuts (2^48) 2803892225 9 Manual.Count131072.C021362.packed 128 cuts21362 = true := by
 decide +kernel
def pointBounds21362 : List (Nat × Nat × Nat) := [(2803970048,100873623013999,100874003880095)]
theorem point_links_checked21362 : (cuts21362.take 1).map (fun c => (2803892225-1+2*2^9*c.k,100873256706181+c.lower,100873637572066+c.upper)) = pointBounds21362 := by
 decide +kernel
def cuts21363 : List PrefixCut := [⟨34,156595733,156595827⟩,
⟨120,562330438,562330763⟩,
⟨128,598566885,598567230⟩]
theorem checked21363 : checkPrefixCuts (2^48) 2804023297 9 Manual.Count131072.C021363.packed 128 cuts21363 = true := by
 decide +kernel
def pointBounds21363 : List (Nat × Nat × Nat) := [(2804058112,100874020329257,100874401195588),(2804146176,100874426063962,100874806930524)]
theorem point_links_checked21363 : (cuts21363.take 2).map (fun c => (2804023297-1+2*2^9*c.k,100873863733524+c.lower,100874244599761+c.upper)) = pointBounds21363 := by
 decide +kernel
def cuts21364 : List PrefixCut := [⟨78,371091473,371091687⟩,
⟨128,604962993,604963342⟩]
theorem checked21364 : checkPrefixCuts (2^48) 2804154369 9 Manual.Count131072.C021364.packed 128 cuts21364 = true := by
 decide +kernel
def pointBounds21364 : List (Nat × Nat × Nat) := [(2804234240,100874833391882,100875214258678)]
theorem point_links_checked21364 : (cuts21364.take 1).map (fun c => (2804154369-1+2*2^9*c.k,100874462300409+c.lower,100874843166991+c.upper)) = pointBounds21364 := by
 decide +kernel
def cuts21365 : List PrefixCut := [⟨36,169227985,169228085⟩,
⟨122,571612266,571612592⟩,
⟨128,601321356,601321698⟩]
theorem checked21365 : checkPrefixCuts (2^48) 2804285441 9 Manual.Count131072.C021365.packed 128 cuts21365 = true := by
 decide +kernel
def pointBounds21365 : List (Nat × Nat × Nat) := [(2804322304,100875236491387,100875617358418),(2804410368,100875638875668,100876019742925)]
theorem point_links_checked21365 : (cuts21365.take 2).map (fun c => (2804285441-1+2*2^9*c.k,100875067263402+c.lower,100875448130333+c.upper)) = pointBounds21365 := by
 decide +kernel
def cuts21366 : List PrefixCut := [⟨80,379587875,379588096⟩,
⟨128,608419235,608419584⟩]
theorem checked21366 : checkPrefixCuts (2^48) 2804416513 9 Manual.Count131072.C021366.packed 128 cuts21366 = true := by
 decide +kernel
def pointBounds21366 : List (Nat × Nat × Nat) := [(2804498432,100876048172633,100876429040127)]
theorem point_links_checked21366 : (cuts21366.take 1).map (fun c => (2804416513-1+2*2^9*c.k,100875668584758+c.lower,100876049452031+c.upper)) = pointBounds21366 := by
 decide +kernel
def cuts21367 : List PrefixCut := [⟨38,178545855,178545963⟩,
⟨124,585709526,585709870⟩,
⟨128,602971296,602971651⟩]
theorem checked21367 : checkPrefixCuts (2^48) 2804547585 9 Manual.Count131072.C021367.packed 128 cuts21367 = true := by
 decide +kernel
def pointBounds21367 : List (Nat × Nat × Nat) := [(2804586496,100876455549848,100876836417578),(2804674560,100876862713519,100877243581485)]
theorem point_links_checked21367 : (cuts21367.take 2).map (fun c => (2804547585-1+2*2^9*c.k,100876277003993+c.lower,100876657871615+c.upper)) = pointBounds21367 := by
 decide +kernel
def cuts21368 : List PrefixCut := [⟨82,386777988,386778215⟩,
⟨128,606957332,606957685⟩]
theorem checked21368 : checkPrefixCuts (2^48) 2804678657 9 Manual.Count131072.C021368.packed 128 cuts21368 = true := by
 decide +kernel
def pointBounds21368 : List (Nat × Nat × Nat) := [(2804762624,100877266753277,100877647621481)]
theorem point_links_checked21368 : (cuts21368.take 1).map (fun c => (2804678657-1+2*2^9*c.k,100876879975289+c.lower,100877260843266+c.upper)) = pointBounds21368 := by
 decide +kernel
def cuts21369 : List PrefixCut := [⟨40,189668378,189668485⟩,
⟨126,596091288,596091631⟩,
⟨128,605022412,605022760⟩]
theorem checked21369 : checkPrefixCuts (2^48) 2804809729 9 Manual.Count131072.C021369.packed 128 cuts21369 = true := by
 decide +kernel
def pointBounds21369 : List (Nat × Nat × Nat) := [(2804850688,100877676600999,100878057469436),(2804938752,100878083023909,100878463892582)]
theorem point_links_checked21369 : (cuts21369.take 2).map (fun c => (2804809729-1+2*2^9*c.k,100877486932621+c.lower,100877867800951+c.upper)) = pointBounds21369 := by
 decide +kernel
def cuts21370 : List PrefixCut := [⟨84,394067173,394067409⟩,
⟨128,610613394,610613750⟩]
theorem checked21370 : checkPrefixCuts (2^48) 2804940801 9 Manual.Count131072.C021370.packed 128 cuts21370 = true := by
 decide +kernel
def pointBounds21370 : List (Nat × Nat × Nat) := [(2805026816,100878486022206,100878866891120)]
theorem point_links_checked21370 : (cuts21370.take 1).map (fun c => (2804940801-1+2*2^9*c.k,100878091955033+c.lower,100878472823711+c.upper)) = pointBounds21370 := by
 decide +kernel
def cuts21371 : List PrefixCut := [⟨42,194567443,194567555⟩,
⟨128,595934945,595935287⟩]
theorem checked21371 : checkPrefixCuts (2^48) 2805071873 9 Manual.Count131072.C021371.packed 128 cuts21371 = true := by
 decide +kernel
def pointBounds21371 : List (Nat × Nat × Nat) := [(2805114880,100878897135870,100879278005016),(2805202944,100879298503372,100879679372748)]
theorem point_links_checked21371 : (cuts21371.take 2).map (fun c => (2805071873-1+2*2^9*c.k,100878702568427+c.lower,100879083437461+c.upper)) = pointBounds21371 := by
 decide +kernel
def cuts21372 : List PrefixCut := [⟨86,406171172,406171412⟩,
⟨128,609653365,609653722⟩]
theorem checked21372 : checkPrefixCuts (2^48) 2805202945 9 Manual.Count131072.C021372.packed 128 cuts21372 = true := by
 decide +kernel
def pointBounds21372 : List (Nat × Nat × Nat) := [(2805291008,100879704674544,100880085544160)]
theorem point_links_checked21372 : (cuts21372.take 1).map (fun c => (2805202945-1+2*2^9*c.k,100879298503372+c.lower,100879679372748+c.upper)) = pointBounds21372 := by
 decide +kernel
def cuts21373 : List PrefixCut := [⟨44,208194716,208194837⟩,
⟨128,600895917,600896262⟩]
theorem checked21373 : checkPrefixCuts (2^48) 2805334017 9 Manual.Count131072.C021373.packed 128 cuts21373 = true := by
 decide +kernel
def pointBounds21373 : List (Nat × Nat × Nat) := [(2805379072,100880116351453,100880497221307)]
theorem point_links_checked21373 : (cuts21373.take 1).map (fun c => (2805334017-1+2*2^9*c.k,100879908156737+c.lower,100880289026470+c.upper)) = pointBounds21373 := by
 decide +kernel
def cuts21374 : List PrefixCut := [⟨2,9531434,9531439⟩,
⟨88,416567283,416567518⟩,
⟨128,609195051,609195392⟩]
theorem checked21374 : checkPrefixCuts (2^48) 2805465089 9 Manual.Count131072.C021374.packed 128 cuts21374 = true := by
 decide +kernel
def pointBounds21374 : List (Nat × Nat × Nat) := [(2805467136,100880518584088,100880899454171),(2805555200,100880925619937,100881306490250)]
theorem point_links_checked21374 : (cuts21374.take 2).map (fun c => (2805465089-1+2*2^9*c.k,100880509052654+c.lower,100880889922732+c.upper)) = pointBounds21374 := by
 decide +kernel
def cuts21375 : List PrefixCut := [⟨46,215799897,215800019⟩,
⟨128,610069499,610069847⟩]
theorem checked21375 : checkPrefixCuts (2^48) 2805596161 9 Manual.Count131072.C021375.packed 128 cuts21375 = true := by
 decide +kernel
def pointBounds21375 : List (Nat × Nat × Nat) := [(2805643264,100881334047602,100881714918143)]
theorem point_links_checked21375 : (cuts21375.take 1).map (fun c => (2805596161-1+2*2^9*c.k,100881118247705+c.lower,100881499118124+c.upper)) = pointBounds21375 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000042
