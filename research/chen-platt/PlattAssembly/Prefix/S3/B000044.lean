import PlattAssemblyKernel
import PlattCertificates.Count131072.C021408
import PlattCertificates.Count131072.C021409
import PlattCertificates.Count131072.C021410
import PlattCertificates.Count131072.C021411
import PlattCertificates.Count131072.C021412
import PlattCertificates.Count131072.C021413
import PlattCertificates.Count131072.C021414
import PlattCertificates.Count131072.C021415
import PlattCertificates.Count131072.C021416
import PlattCertificates.Count131072.C021417
import PlattCertificates.Count131072.C021418
import PlattCertificates.Count131072.C021419
import PlattCertificates.Count131072.C021420
import PlattCertificates.Count131072.C021421
import PlattCertificates.Count131072.C021422
import PlattCertificates.Count131072.C021423
import PlattCertificates.Count131072.C021424
import PlattCertificates.Count131072.C021425
import PlattCertificates.Count131072.C021426
import PlattCertificates.Count131072.C021427
import PlattCertificates.Count131072.C021428
import PlattCertificates.Count131072.C021429
import PlattCertificates.Count131072.C021430
import PlattCertificates.Count131072.C021431
import PlattCertificates.Count131072.C021432
import PlattCertificates.Count131072.C021433
import PlattCertificates.Count131072.C021434
import PlattCertificates.Count131072.C021435
import PlattCertificates.Count131072.C021436
import PlattCertificates.Count131072.C021437
import PlattCertificates.Count131072.C021438
import PlattCertificates.Count131072.C021439
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000044
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts21408 : List PrefixCut := [⟨36,172494715,172494819⟩,
⟨122,575073570,575073904⟩,
⟨128,605324075,605324425⟩]
theorem checked21408 : checkPrefixCuts (2^48) 2809921537 9 Manual.Count131072.C021408.packed 128 cuts21408 = true := by
 decide +kernel
def pointBounds21408 : List (Nat × Nat × Nat) := [(2809958400,100901226160280,100901607042289),(2810046464,100901628739135,100902009621374)]
theorem point_links_checked21408 : (cuts21408.take 2).map (fun c => (2809921537-1+2*2^9*c.k,100901053665565+c.lower,100901434547470+c.upper)) = pointBounds21408 := by
 decide +kernel
def cuts21409 : List PrefixCut := [⟨80,372516136,372516351⟩,
⟨128,597683316,597683660⟩]
theorem checked21409 : checkPrefixCuts (2^48) 2810052609 9 Manual.Count131072.C021409.packed 128 cuts21409 = true := by
 decide +kernel
def pointBounds21409 : List (Nat × Nat × Nat) := [(2810134528,100902031505776,100902412388246)]
theorem point_links_checked21409 : (cuts21409.take 1).map (fun c => (2810052609-1+2*2^9*c.k,100901658989640+c.lower,100902039871895+c.upper)) = pointBounds21409 := by
 decide +kernel
def cuts21410 : List PrefixCut := [⟨38,177486666,177486768⟩,
⟨124,585336176,585336514⟩,
⟨128,603364589,603364938⟩]
theorem checked21410 : checkPrefixCuts (2^48) 2810183681 9 Manual.Count131072.C021410.packed 128 cuts21410 = true := by
 decide +kernel
def pointBounds21410 : List (Nat × Nat × Nat) := [(2810222592,100902434159622,100902815042323),(2810310656,100902842009132,100903222892069)]
theorem point_links_checked21410 : (cuts21410.take 2).map (fun c => (2810183681-1+2*2^9*c.k,100902256672956+c.lower,100902637555555+c.upper)) = pointBounds21410 := by
 decide +kernel
def cuts21411 : List PrefixCut := [⟨82,386803541,386803758⟩,
⟨128,605639901,605640243⟩]
theorem checked21411 : checkPrefixCuts (2^48) 2810314753 9 Manual.Count131072.C021411.packed 128 cuts21411 = true := by
 decide +kernel
def pointBounds21411 : List (Nat × Nat × Nat) := [(2810398720,100903246841086,100903627724251)]
theorem point_links_checked21411 : (cuts21411.take 1).map (fun c => (2810314753-1+2*2^9*c.k,100902860037545+c.lower,100903240920493+c.upper)) = pointBounds21411 := by
 decide +kernel
def cuts21412 : List PrefixCut := [⟨40,184480678,184480787⟩,
⟨126,586282792,586283139⟩,
⟨128,594595116,594595467⟩]
theorem checked21412 : checkPrefixCuts (2^48) 2810445825 9 Manual.Count131072.C021412.packed 128 cuts21412 = true := by
 decide +kernel
def pointBounds21412 : List (Nat × Nat × Nat) := [(2810486784,100903650158124,100904031041523),(2810574848,100904051960238,100904432843875)]
theorem point_links_checked21412 : (cuts21412.take 2).map (fun c => (2810445825-1+2*2^9*c.k,100903465677446+c.lower,100903846560736+c.upper)) = pointBounds21412 := by
 decide +kernel
def cuts21413 : List PrefixCut := [⟨84,393577372,393577598⟩,
⟨128,594767784,594768120⟩]
theorem checked21413 : checkPrefixCuts (2^48) 2810576897 9 Manual.Count131072.C021413.packed 128 cuts21413 = true := by
 decide +kernel
def pointBounds21413 : List (Nat × Nat × Nat) := [(2810662912,100904453849934,100904834733801)]
theorem point_links_checked21413 : (cuts21413.take 1).map (fun c => (2810576897-1+2*2^9*c.k,100904060272562+c.lower,100904441156203+c.upper)) = pointBounds21413 := by
 decide +kernel
def cuts21414 : List PrefixCut := [⟨42,200386153,200386268⟩,
⟨128,611163110,611163459⟩]
theorem checked21414 : checkPrefixCuts (2^48) 2810707969 9 Manual.Count131072.C021414.packed 128 cuts21414 = true := by
 decide +kernel
def pointBounds21414 : List (Nat × Nat × Nat) := [(2810750976,100904855426499,100905236310591),(2810839040,100905266203456,100905647087782)]
theorem point_links_checked21414 : (cuts21414.take 2).map (fun c => (2810707969-1+2*2^9*c.k,100904655040346+c.lower,100905035924323+c.upper)) = pointBounds21414 := by
 decide +kernel
def cuts21415 : List PrefixCut := [⟨86,404856028,404856266⟩,
⟨128,600420054,600420402⟩]
theorem checked21415 : checkPrefixCuts (2^48) 2810839041 9 Manual.Count131072.C021415.packed 128 cuts21415 = true := by
 decide +kernel
def pointBounds21415 : List (Nat × Nat × Nat) := [(2810927104,100905671059484,100906051944048)]
theorem point_links_checked21415 : (cuts21415.take 1).map (fun c => (2810839041-1+2*2^9*c.k,100905266203456+c.lower,100905647087782+c.upper)) = pointBounds21415 := by
 decide +kernel
def cuts21416 : List PrefixCut := [⟨44,209279295,209279414⟩,
⟨128,607301227,607301578⟩]
theorem checked21416 : checkPrefixCuts (2^48) 2810970113 9 Manual.Count131072.C021416.packed 128 cuts21416 = true := by
 decide +kernel
def pointBounds21416 : List (Nat × Nat × Nat) := [(2811015168,100906075902805,100906456787598)]
theorem point_links_checked21416 : (cuts21416.take 1).map (fun c => (2810970113-1+2*2^9*c.k,100905866623510+c.lower,100906247508184+c.upper)) = pointBounds21416 := by
 decide +kernel
def cuts21417 : List PrefixCut := [⟨2,7609859,7609864⟩,
⟨88,413028580,413028817⟩,
⟨128,603367786,603368131⟩]
theorem checked21417 : checkPrefixCuts (2^48) 2811101185 9 Manual.Count131072.C021417.packed 128 cuts21417 = true := by
 decide +kernel
def pointBounds21417 : List (Nat × Nat × Nat) := [(2811103232,100906481534596,100906862419626),(2811191296,100906886953317,100907267838579)]
theorem point_links_checked21417 : (cuts21417.take 2).map (fun c => (2811101185-1+2*2^9*c.k,100906473924737+c.lower,100906854809762+c.upper)) = pointBounds21417 := by
 decide +kernel
def cuts21418 : List PrefixCut := [⟨46,211162037,211162162⟩,
⟨128,591324965,591325311⟩]
theorem checked21418 : checkPrefixCuts (2^48) 2811232257 9 Manual.Count131072.C021418.packed 128 cuts21418 = true := by
 decide +kernel
def pointBounds21418 : List (Nat × Nat × Nat) := [(2811279360,100907288454560,100907669340055)]
theorem point_links_checked21418 : (cuts21418.take 1).map (fun c => (2811232257-1+2*2^9*c.k,100907077292523+c.lower,100907458177893+c.upper)) = pointBounds21418 := by
 decide +kernel
def cuts21419 : List PrefixCut := [⟨4,18422144,18422156⟩,
⟨90,423602617,423602861⟩,
⟨128,602010148,602010496⟩]
theorem checked21419 : checkPrefixCuts (2^48) 2811363329 9 Manual.Count131072.C021419.packed 128 cuts21419 = true := by
 decide +kernel
def pointBounds21419 : List (Nat × Nat × Nat) := [(2811367424,100907687039632,100908067925360),(2811455488,100908092220105,100908473106065)]
theorem point_links_checked21419 : (cuts21419.take 2).map (fun c => (2811363329-1+2*2^9*c.k,100907668617488+c.lower,100908049503204+c.upper)) = pointBounds21419 := by
 decide +kernel
def cuts21420 : List PrefixCut := [⟨48,228662417,228662546⟩,
⟨128,601281311,601281653⟩]
theorem checked21420 : checkPrefixCuts (2^48) 2811494401 9 Manual.Count131072.C021420.packed 128 cuts21420 = true := by
 decide +kernel
def pointBounds21420 : List (Nat × Nat × Nat) := [(2811543552,100908499290053,100908880176246)]
theorem point_links_checked21420 : (cuts21420.take 1).map (fun c => (2811494401-1+2*2^9*c.k,100908270627636+c.lower,100908651513700+c.upper)) = pointBounds21420 := by
 decide +kernel
def cuts21421 : List PrefixCut := [⟨6,28231298,28231315⟩,
⟨92,429068919,429069177⟩,
⟨128,595647076,595647433⟩]
theorem checked21421 : checkPrefixCuts (2^48) 2811625473 9 Manual.Count131072.C021421.packed 128 cuts21421 = true := by
 decide +kernel
def pointBounds21421 : List (Nat × Nat × Nat) := [(2811631616,100908900140245,100909281026668),(2811719680,100909300977866,100909681864530)]
theorem point_links_checked21421 : (cuts21421.take 2).map (fun c => (2811625473-1+2*2^9*c.k,100908871908947+c.lower,100909252795353+c.upper)) = pointBounds21421 := by
 decide +kernel
def cuts21422 : List PrefixCut := [⟨50,235948714,235948845⟩,
⟨128,614338766,614339114⟩]
theorem checked21422 : checkPrefixCuts (2^48) 2811756545 9 Manual.Count131072.C021422.packed 128 cuts21422 = true := by
 decide +kernel
def pointBounds21422 : List (Nat × Nat × Nat) := [(2811807744,100909703504737,100910084391631)]
theorem point_links_checked21422 : (cuts21422.take 1).map (fun c => (2811756545-1+2*2^9*c.k,100909467556023+c.lower,100909848442786+c.upper)) = pointBounds21422 := by
 decide +kernel
def cuts21423 : List PrefixCut := [⟨8,36537087,36537108⟩,
⟨94,442742526,442742779⟩,
⟨128,604600520,604600865⟩]
theorem checked21423 : checkPrefixCuts (2^48) 2811887617 9 Manual.Count131072.C021423.packed 128 cuts21423 = true := by
 decide +kernel
def pointBounds21423 : List (Nat × Nat × Nat) := [(2811895808,100910118431876,100910499319008),(2811983872,100910524637315,100910905524679)]
theorem point_links_checked21423 : (cuts21423.take 2).map (fun c => (2811887617-1+2*2^9*c.k,100910081894789+c.lower,100910462781900+c.upper)) = pointBounds21423 := by
 decide +kernel
def cuts21424 : List PrefixCut := [⟨52,245035335,245035474⟩,
⟨128,604772414,604772761⟩]
theorem checked21424 : checkPrefixCuts (2^48) 2812018689 9 Manual.Count131072.C021424.packed 128 cuts21424 = true := by
 decide +kernel
def pointBounds21424 : List (Nat × Nat × Nat) := [(2812071936,100910931530644,100911312418239)]
theorem point_links_checked21424 : (cuts21424.take 1).map (fun c => (2812018689-1+2*2^9*c.k,100910686495309+c.lower,100911067382765+c.upper)) = pointBounds21424 := by
 decide +kernel
def cuts21425 : List PrefixCut := [⟨10,47243538,47243565⟩,
⟨96,447605524,447605783⟩,
⟨128,601741568,601741916⟩]
theorem checked21425 : checkPrefixCuts (2^48) 2812149761 9 Manual.Count131072.C021425.packed 128 cuts21425 = true := by
 decide +kernel
def pointBounds21425 : List (Nat × Nat × Nat) := [(2812160000,100911338511261,100911719399091),(2812248064,100911738873247,100912119761309)]
theorem point_links_checked21425 : (cuts21425.take 2).map (fun c => (2812149761-1+2*2^9*c.k,100911291267723+c.lower,100911672155526+c.upper)) = pointBounds21425 := by
 decide +kernel
def cuts21426 : List PrefixCut := [⟨54,250216955,250217097⟩,
⟨128,593906932,593907268⟩]
theorem checked21426 : checkPrefixCuts (2^48) 2812280833 9 Manual.Count131072.C021426.packed 128 cuts21426 = true := by
 decide +kernel
def pointBounds21426 : List (Nat × Nat × Nat) := [(2812336128,100912143226246,100912524114539)]
theorem point_links_checked21426 : (cuts21426.take 1).map (fun c => (2812280833-1+2*2^9*c.k,100911893009291+c.lower,100912273897442+c.upper)) = pointBounds21426 := by
 decide +kernel
def cuts21427 : List PrefixCut := [⟨12,57847903,57847938⟩,
⟨98,467379731,467379996⟩,
⟨128,607590381,607590728⟩]
theorem checked21427 : checkPrefixCuts (2^48) 2812411905 9 Manual.Count131072.C021427.packed 128 cuts21427 = true := by
 decide +kernel
def pointBounds21427 : List (Nat × Nat × Nat) := [(2812424192,100912544764126,100912925652648),(2812512256,100912954295954,100913335184706)]
theorem point_links_checked21427 : (cuts21427.take 2).map (fun c => (2812411905-1+2*2^9*c.k,100912486916223+c.lower,100912867804710+c.upper)) = pointBounds21427 := by
 decide +kernel
def cuts21428 : List PrefixCut := [⟨56,268107406,268107558⟩,
⟨128,606261114,606261461⟩]
theorem checked21428 : checkPrefixCuts (2^48) 2812542977 9 Manual.Count131072.C021428.packed 128 cuts21428 = true := by
 decide +kernel
def pointBounds21428 : List (Nat × Nat × Nat) := [(2812600320,100913362614010,100913743502996)]
theorem point_links_checked21428 : (cuts21428.take 1).map (fun c => (2812542977-1+2*2^9*c.k,100913094506604+c.lower,100913475395438+c.upper)) = pointBounds21428 := by
 decide +kernel
def cuts21429 : List PrefixCut := [⟨14,69751239,69751280⟩,
⟨100,479945142,479945411⟩,
⟨128,605632575,605632916⟩]
theorem checked21429 : checkPrefixCuts (2^48) 2812674049 9 Manual.Count131072.C021429.packed 128 cuts21429 = true := by
 decide +kernel
def pointBounds21429 : List (Nat × Nat × Nat) := [(2812688384,100913770518957,100914151408179),(2812776448,100914180712860,100914561602310)]
theorem point_links_checked21429 : (cuts21429.take 2).map (fun c => (2812674049-1+2*2^9*c.k,100913700767718+c.lower,100914081656899+c.upper)) = pointBounds21429 := by
 decide +kernel
def cuts21430 : List PrefixCut := [⟨58,269283154,269283317⟩,
⟨128,597698918,597699268⟩]
theorem checked21430 : checkPrefixCuts (2^48) 2812805121 9 Manual.Count131072.C021430.packed 128 cuts21430 = true := by
 decide +kernel
def pointBounds21430 : List (Nat × Nat × Nat) := [(2812864512,100914575683447,100914956573132)]
theorem point_links_checked21430 : (cuts21430.take 1).map (fun c => (2812805121-1+2*2^9*c.k,100914306400293+c.lower,100914687289815+c.upper)) = pointBounds21430 := by
 decide +kernel
def cuts21431 : List PrefixCut := [⟨16,76449010,76449056⟩,
⟨102,482301612,482301891⟩,
⟨128,601373316,601373660⟩]
theorem checked21431 : checkPrefixCuts (2^48) 2812936193 9 Manual.Count131072.C021431.packed 128 cuts21431 = true := by
 decide +kernel
def pointBounds21431 : List (Nat × Nat × Nat) := [(2812952576,100914980548221,100915361438139),(2813040640,100915386400823,100915767290974)]
theorem point_links_checked21431 : (cuts21431.take 2).map (fun c => (2812936193-1+2*2^9*c.k,100914904099211+c.lower,100915284989083+c.upper)) = pointBounds21431 := by
 decide +kernel
def cuts21432 : List PrefixCut := [⟨60,283866498,283866651⟩,
⟨128,608249244,608249581⟩]
theorem checked21432 : checkPrefixCuts (2^48) 2813067265 9 Manual.Count131072.C021432.packed 128 cuts21432 = true := by
 decide +kernel
def pointBounds21432 : List (Nat × Nat × Nat) := [(2813128704,100915789339025,100916170229394)]
theorem point_links_checked21432 : (cuts21432.take 1).map (fun c => (2813067265-1+2*2^9*c.k,100915505472527+c.lower,100915886362743+c.upper)) = pointBounds21432 := by
 decide +kernel
def cuts21433 : List PrefixCut := [⟨18,86047125,86047173⟩,
⟨104,488559955,488560238⟩,
⟨128,601517403,601517750⟩]
theorem checked21433 : checkPrefixCuts (2^48) 2813198337 9 Manual.Count131072.C021433.packed 128 cuts21433 = true := by
 decide +kernel
def pointBounds21433 : List (Nat × Nat × Nat) := [(2813216768,100916199768896,100916580659497),(2813304832,100916602281726,100916983172562)]
theorem point_links_checked21433 : (cuts21433.take 2).map (fun c => (2813198337-1+2*2^9*c.k,100916113721771+c.lower,100916494612324+c.upper)) = pointBounds21433 := by
 decide +kernel
def cuts21434 : List PrefixCut := [⟨62,294345080,294345246⟩,
⟨128,605291153,605291500⟩]
theorem checked21434 : checkPrefixCuts (2^48) 2813329409 9 Manual.Count131072.C021434.packed 128 cuts21434 = true := by
 decide +kernel
def pointBounds21434 : List (Nat × Nat × Nat) := [(2813392896,100917009584254,100917390475320)]
theorem point_links_checked21434 : (cuts21434.take 1).map (fun c => (2813329409-1+2*2^9*c.k,100916715239174+c.lower,100917096130074+c.upper)) = pointBounds21434 := by
 decide +kernel
def cuts21435 : List PrefixCut := [⟨20,93042248,93042300⟩,
⟨106,492315831,492316120⟩,
⟨128,598760028,598760380⟩]
theorem checked21435 : checkPrefixCuts (2^48) 2813460481 9 Manual.Count131072.C021435.packed 128 cuts21435 = true := by
 decide +kernel
def pointBounds21435 : List (Nat × Nat × Nat) := [(2813480960,100917413572575,100917794463874),(2813569024,100917812846158,100918193737694)]
theorem point_links_checked21435 : (cuts21435.take 2).map (fun c => (2813460481-1+2*2^9*c.k,100917320530327+c.lower,100917701421574+c.upper)) = pointBounds21435 := by
 decide +kernel
def cuts21436 : List PrefixCut := [⟨64,295918268,295918439⟩,
⟨128,596431238,596431589⟩]
theorem checked21436 : checkPrefixCuts (2^48) 2813591553 9 Manual.Count131072.C021436.packed 128 cuts21436 = true := by
 decide +kernel
def pointBounds21436 : List (Nat × Nat × Nat) := [(2813657088,100918215208623,100918596100393)]
theorem point_links_checked21436 : (cuts21436.take 1).map (fun c => (2813591553-1+2*2^9*c.k,100917919290355+c.lower,100918300181954+c.upper)) = pointBounds21436 := by
 decide +kernel
def cuts21437 : List PrefixCut := [⟨22,103437311,103437369⟩,
⟨108,507275036,507275328⟩,
⟨128,605206540,605206889⟩]
theorem checked21437 : checkPrefixCuts (2^48) 2813722625 9 Manual.Count131072.C021437.packed 128 cuts21437 = true := by
 decide +kernel
def pointBounds21437 : List (Nat × Nat × Nat) := [(2813745152,100918619158904,100919000050912),(2813833216,100919022996629,100919403888871)]
theorem point_links_checked21437 : (cuts21437.take 2).map (fun c => (2813722625-1+2*2^9*c.k,100918515721593+c.lower,100918896613543+c.upper)) = pointBounds21437 := by
 decide +kernel
def cuts21438 : List PrefixCut := [⟨66,309094583,309094763⟩,
⟨128,599076617,599076967⟩]
theorem checked21438 : checkPrefixCuts (2^48) 2813853697 9 Manual.Count131072.C021438.packed 128 cuts21438 = true := by
 decide +kernel
def pointBounds21438 : List (Nat × Nat × Nat) := [(2813921280,100919430022716,100919810915195)]
theorem point_links_checked21438 : (cuts21438.take 1).map (fun c => (2813853697-1+2*2^9*c.k,100919120928133+c.lower,100919501820432+c.upper)) = pointBounds21438 := by
 decide +kernel
def cuts21439 : List PrefixCut := [⟨24,114430571,114430634⟩,
⟨110,518230380,518230673⟩,
⟨128,604350033,604350375⟩]
theorem checked21439 : checkPrefixCuts (2^48) 2813984769 9 Manual.Count131072.C021439.packed 128 cuts21439 = true := by
 decide +kernel
def pointBounds21439 : List (Nat × Nat × Nat) := [(2814009344,100919834435321,100920215328033),(2814097408,100920238235130,100920619128072)]
theorem point_links_checked21439 : (cuts21439.take 2).map (fun c => (2813984769-1+2*2^9*c.k,100919720004750+c.lower,100920100897399+c.upper)) = pointBounds21439 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000044
