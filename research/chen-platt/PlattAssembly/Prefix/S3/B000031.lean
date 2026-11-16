import PlattAssemblyKernel
import PlattCertificates.Count131072.C020992
import PlattCertificates.Count131072.C020993
import PlattCertificates.Count131072.C020994
import PlattCertificates.Count131072.C020995
import PlattCertificates.Count131072.C020996
import PlattCertificates.Count131072.C020997
import PlattCertificates.Count131072.C020998
import PlattCertificates.Count131072.C020999
import PlattCertificates.Count131072.C021000
import PlattCertificates.Count131072.C021001
import PlattCertificates.Count131072.C021002
import PlattCertificates.Count131072.C021003
import PlattCertificates.Count131072.C021004
import PlattCertificates.Count131072.C021005
import PlattCertificates.Count131072.C021006
import PlattCertificates.Count131072.C021007
import PlattCertificates.Count131072.C021008
import PlattCertificates.Count131072.C021009
import PlattCertificates.Count131072.C021010
import PlattCertificates.Count131072.C021011
import PlattCertificates.Count131072.C021012
import PlattCertificates.Count131072.C021013
import PlattCertificates.Count131072.C021014
import PlattCertificates.Count131072.C021015
import PlattCertificates.Count131072.C021016
import PlattCertificates.Count131072.C021017
import PlattCertificates.Count131072.C021018
import PlattCertificates.Count131072.C021019
import PlattCertificates.Count131072.C021020
import PlattCertificates.Count131072.C021021
import PlattCertificates.Count131072.C021022
import PlattCertificates.Count131072.C021023
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000031
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts20992 : List PrefixCut := [⟨50,239446941,239447082⟩,
⟨128,618426087,618426447⟩]
theorem checked20992 : checkPrefixCuts (2^48) 2755395585 9 Manual.Count131072.C020992.packed 128 cuts20992 = true := by
 decide +kernel
def pointBounds20992 : List (Nat × Nat × Nat) := [(2755446784,100647614622419,100647995357873)]
theorem point_links_checked20992 : (cuts20992.take 1).map (fun c => (2755395585-1+2*2^9*c.k,100647375175478+c.lower,100647755910791+c.upper)) = pointBounds20992 := by
 decide +kernel
def cuts20993 : List PrefixCut := [⟨7,32892008,32892027⟩,
⟨92,445873665,445873924⟩,
⟨128,620030966,620031323⟩]
theorem checked20993 : checkPrefixCuts (2^48) 2755526657 9 Manual.Count131072.C020993.packed 128 cuts20993 = true := by
 decide +kernel
def pointBounds20993 : List (Nat × Nat × Nat) := [(2755533824,100648026493573,100648407229265),(2755620864,100648439475230,100648820211162)]
theorem point_links_checked20993 : (cuts20993.take 2).map (fun c => (2755526657-1+2*2^9*c.k,100647993601565+c.lower,100648374337238+c.upper)) = pointBounds20993 := by
 decide +kernel
def cuts20994 : List PrefixCut := [⟨49,236359900,236360035⟩,
⟨128,614588042,614588395⟩]
theorem checked20994 : checkPrefixCuts (2^48) 2755657729 9 Manual.Count131072.C020994.packed 128 cuts20994 = true := by
 decide +kernel
def pointBounds20994 : List (Nat × Nat × Nat) := [(2755707904,100648849992431,100649230728596)]
theorem point_links_checked20994 : (cuts20994.take 1).map (fun c => (2755657729-1+2*2^9*c.k,100648613632531+c.lower,100648994368561+c.upper)) = pointBounds20994 := by
 decide +kernel
def cuts20995 : List PrefixCut := [⟨6,30131122,30131138⟩,
⟨91,438681738,438681996⟩,
⟨128,618235648,618236012⟩]
theorem checked20995 : checkPrefixCuts (2^48) 2755788801 9 Manual.Count131072.C020995.packed 128 cuts20995 = true := by
 decide +kernel
def pointBounds20995 : List (Nat × Nat × Nat) := [(2755794944,100649258351695,100649639088094),(2755881984,100649666902311,100650047638952)]
theorem point_links_checked20995 : (cuts20995.take 2).map (fun c => (2755788801-1+2*2^9*c.k,100649228220573+c.lower,100649608956956+c.upper)) = pointBounds20995 := by
 decide +kernel
def cuts20996 : List PrefixCut := [⟨48,228268881,228269010⟩,
⟨128,616265683,616266035⟩]
theorem checked20996 : checkPrefixCuts (2^48) 2755919873 9 Manual.Count131072.C020996.packed 128 cuts20996 = true := by
 decide +kernel
def pointBounds20996 : List (Nat × Nat × Nat) := [(2755969024,100650074725102,100650455461978)]
theorem point_links_checked20996 : (cuts20996.take 1).map (fun c => (2755919873-1+2*2^9*c.k,100649846456221+c.lower,100650227192968+c.upper)) = pointBounds20996 := by
 decide +kernel
def cuts20997 : List PrefixCut := [⟨5,24408996,24409012⟩,
⟨90,444154996,444155253⟩,
⟨128,626551416,626551782⟩]
theorem checked20997 : checkPrefixCuts (2^48) 2756050945 9 Manual.Count131072.C020997.packed 128 cuts20997 = true := by
 decide +kernel
def pointBounds20997 : List (Nat × Nat × Nat) := [(2756056064,100650487130900,100650867868015),(2756143104,100650906876900,100651287614256)]
theorem point_links_checked20997 : (cuts20997.take 2).map (fun c => (2756050945-1+2*2^9*c.k,100650462721904+c.lower,100650843459003+c.upper)) = pointBounds20997 := by
 decide +kernel
def cuts20998 : List PrefixCut := [⟨47,229472722,229472854⟩,
⟨128,620087889,620088244⟩]
theorem checked20998 : checkPrefixCuts (2^48) 2756182017 9 Manual.Count131072.C020998.packed 128 cuts20998 = true := by
 decide +kernel
def pointBounds20998 : List (Nat × Nat × Nat) := [(2756230144,100651318746042,100651699483639)]
theorem point_links_checked20998 : (cuts20998.take 1).map (fun c => (2756182017-1+2*2^9*c.k,100651089273320+c.lower,100651470010785+c.upper)) = pointBounds20998 := by
 decide +kernel
def cuts20999 : List PrefixCut := [⟨4,18892199,18892211⟩,
⟨89,420421425,420421668⟩,
⟨128,607191501,607191853⟩]
theorem checked20999 : checkPrefixCuts (2^48) 2756313089 9 Manual.Count131072.C020999.packed 128 cuts20999 = true := by
 decide +kernel
def pointBounds20999 : List (Nat × Nat × Nat) := [(2756317184,100651728253408,100652108991240),(2756404224,100652129782634,100652510520697)]
theorem point_links_checked20999 : (cuts20999.take 2).map (fun c => (2756313089-1+2*2^9*c.k,100651709361209+c.lower,100652090099029+c.upper)) = pointBounds20999 := by
 decide +kernel
def cuts21000 : List PrefixCut := [⟨46,218422568,218422692⟩,
⟨128,616352667,616353020⟩]
theorem checked21000 : checkPrefixCuts (2^48) 2756444161 9 Manual.Count131072.C021000.packed 128 cuts21000 = true := by
 decide +kernel
def pointBounds21000 : List (Nat × Nat × Nat) := [(2756491264,100652534975278,100652915713574)]
theorem point_links_checked21000 : (cuts21000.take 1).map (fun c => (2756444161-1+2*2^9*c.k,100652316552710+c.lower,100652697290882+c.upper)) = pointBounds21000 := by
 decide +kernel
def cuts21001 : List PrefixCut := [⟨3,15724987,15724996⟩,
⟨88,427529106,427529352⟩,
⟨128,615404637,615404992⟩]
theorem checked21001 : checkPrefixCuts (2^48) 2756575233 9 Manual.Count131072.C021001.packed 128 cuts21001 = true := by
 decide +kernel
def pointBounds21001 : List (Nat × Nat × Nat) := [(2756578304,100652948630364,100653329368898),(2756665344,100653360434483,100653741173254)]
theorem point_links_checked21001 : (cuts21001.take 2).map (fun c => (2756575233-1+2*2^9*c.k,100652932905377+c.lower,100653313643902+c.upper)) = pointBounds21001 := by
 decide +kernel
def cuts21002 : List PrefixCut := [⟨45,218503962,218504088⟩,
⟨128,623951890,623952242⟩]
theorem checked21002 : checkPrefixCuts (2^48) 2756706305 9 Manual.Count131072.C021002.packed 128 cuts21002 = true := by
 decide +kernel
def pointBounds21002 : List (Nat × Nat × Nat) := [(2756752384,100653766813976,100654147552982)]
theorem point_links_checked21002 : (cuts21002.take 1).map (fun c => (2756706305-1+2*2^9*c.k,100653548310014+c.lower,100653929048894+c.upper)) = pointBounds21002 := by
 decide +kernel
def cuts21003 : List PrefixCut := [⟨2,9291155,9291161⟩,
⟨87,422383478,422383718⟩,
⟨128,617387941,617388292⟩]
theorem checked21003 : checkPrefixCuts (2^48) 2756837377 9 Manual.Count131072.C021003.packed 128 cuts21003 = true := by
 decide +kernel
def pointBounds21003 : List (Nat × Nat × Nat) := [(2756839424,100654181553059,100654562292297),(2756926464,100654594645382,100654975384854)]
theorem point_links_checked21003 : (cuts21003.take 2).map (fun c => (2756837377-1+2*2^9*c.k,100654172261904+c.lower,100654553001136+c.upper)) = pointBounds21003 := by
 decide +kernel
def cuts21004 : List PrefixCut := [⟨44,210417714,210417839⟩,
⟨128,613274838,613275195⟩]
theorem checked21004 : checkPrefixCuts (2^48) 2756968449 9 Manual.Count131072.C021004.packed 128 cuts21004 = true := by
 decide +kernel
def pointBounds21004 : List (Nat × Nat × Nat) := [(2757013504,100655000067559,100655380807267)]
theorem point_links_checked21004 : (cuts21004.take 1).map (fun c => (2756968449-1+2*2^9*c.k,100654789649845+c.lower,100655170389428+c.upper)) = pointBounds21004 := by
 decide +kernel
def cuts21005 : List PrefixCut := [⟨1,5512910,5512913⟩,
⟨86,416116139,416116381⟩,
⟨128,623250433,623250797⟩]
theorem checked21005 : checkPrefixCuts (2^48) 2757099521 9 Manual.Count131072.C021005.packed 128 cuts21005 = true := by
 decide +kernel
def pointBounds21005 : List (Nat × Nat × Nat) := [(2757100544,100655408437593,100655789177536),(2757187584,100655819040822,100656199781004)]
theorem point_links_checked21005 : (cuts21005.take 2).map (fun c => (2757099521-1+2*2^9*c.k,100655402924683+c.lower,100655783664623+c.upper)) = pointBounds21005 := by
 decide +kernel
def cuts21006 : List PrefixCut := [⟨43,206722691,206722811⟩,
⟨128,613012499,613012853⟩]
theorem checked21006 : checkPrefixCuts (2^48) 2757230593 9 Manual.Count131072.C021006.packed 128 cuts21006 = true := by
 decide +kernel
def pointBounds21006 : List (Nat × Nat × Nat) := [(2757274624,100656232897807,100656613638231),(2757361664,100656639187615,100657019928273)]
theorem point_links_checked21006 : (cuts21006.take 2).map (fun c => (2757230593-1+2*2^9*c.k,100656026175116+c.lower,100656406915420+c.upper)) = pointBounds21006 := by
 decide +kernel
def cuts21007 : List PrefixCut := [⟨85,409339269,409339502⟩,
⟨128,618087162,618087513⟩]
theorem checked21007 : checkPrefixCuts (2^48) 2757361665 9 Manual.Count131072.C021007.packed 128 cuts21007 = true := by
 decide +kernel
def pointBounds21007 : List (Nat × Nat × Nat) := [(2757448704,100657048526884,100657429267775)]
theorem point_links_checked21007 : (cuts21007.take 1).map (fun c => (2757361665-1+2*2^9*c.k,100656639187615+c.lower,100657019928273+c.upper)) = pointBounds21007 := by
 decide +kernel
def cuts21008 : List PrefixCut := [⟨42,198843242,198843358⟩,
⟨127,608360859,608361213⟩,
⟨128,612852007,612852364⟩]
theorem checked21008 : checkPrefixCuts (2^48) 2757492737 9 Manual.Count131072.C021008.packed 128 cuts21008 = true := by
 decide +kernel
def pointBounds21008 : List (Nat × Nat × Nat) := [(2757535744,100657456118019,100657836859144),(2757622784,100657865635636,100658246376999)]
theorem point_links_checked21008 : (cuts21008.take 2).map (fun c => (2757492737-1+2*2^9*c.k,100657257274777+c.lower,100657638015786+c.upper)) = pointBounds21008 := by
 decide +kernel
def cuts21009 : List PrefixCut := [⟨84,408790059,408790292⟩,
⟨128,619763616,619763969⟩]
theorem checked21009 : checkPrefixCuts (2^48) 2757623809 9 Manual.Count131072.C021009.packed 128 cuts21009 = true := by
 decide +kernel
def pointBounds21009 : List (Nat × Nat × Nat) := [(2757709824,100658278916843,100658659658442)]
theorem point_links_checked21009 : (cuts21009.take 1).map (fun c => (2757623809-1+2*2^9*c.k,100657870126784+c.lower,100658250868150+c.upper)) = pointBounds21009 := by
 decide +kernel
def cuts21010 : List PrefixCut := [⟨41,198620271,198620386⟩,
⟨126,612385776,612386128⟩,
⟨128,622694025,622694382⟩]
theorem checked21010 : checkPrefixCuts (2^48) 2757754881 9 Manual.Count131072.C021010.packed 128 cuts21010 = true := by
 decide +kernel
def pointBounds21010 : List (Nat × Nat × Nat) := [(2757796864,100658688510671,100659069252505),(2757883904,100659102276176,100659483018247)]
theorem point_links_checked21010 : (cuts21010.take 2).map (fun c => (2757754881-1+2*2^9*c.k,100658489890400+c.lower,100658870632119+c.upper)) = pointBounds21010 := by
 decide +kernel
def cuts21011 : List PrefixCut := [⟨83,392523759,392523985⟩,
⟨128,609906953,609907306⟩]
theorem checked21011 : checkPrefixCuts (2^48) 2757885953 9 Manual.Count131072.C021011.packed 128 cuts21011 = true := by
 decide +kernel
def pointBounds21011 : List (Nat × Nat × Nat) := [(2757970944,100659505108184,100659885850486)]
theorem point_links_checked21011 : (cuts21011.take 1).map (fun c => (2757885953-1+2*2^9*c.k,100659112584425+c.lower,100659493326501+c.upper)) = pointBounds21011 := by
 decide +kernel
def cuts21012 : List PrefixCut := [⟨40,188804032,188804140⟩,
⟨125,598652322,598652671⟩,
⟨128,612735525,612735882⟩]
theorem checked21012 : checkPrefixCuts (2^48) 2758017025 9 Manual.Count131072.C021012.packed 128 cuts21012 = true := by
 decide +kernel
def pointBounds21012 : List (Nat × Nat × Nat) := [(2758057984,100659911295410,100660292037947),(2758145024,100660321143700,100660701886478)]
theorem point_links_checked21012 : (cuts21012.take 2).map (fun c => (2758017025-1+2*2^9*c.k,100659722491378+c.lower,100660103233807+c.upper)) = pointBounds21012 := by
 decide +kernel
def cuts21013 : List PrefixCut := [⟨82,396466518,396466754⟩,
⟨128,618421270,618421631⟩]
theorem checked21013 : checkPrefixCuts (2^48) 2758148097 9 Manual.Count131072.C021013.packed 128 cuts21013 = true := by
 decide +kernel
def pointBounds21013 : List (Nat × Nat × Nat) := [(2758232064,100660731693421,100661112436443)]
theorem point_links_checked21013 : (cuts21013.take 1).map (fun c => (2758148097-1+2*2^9*c.k,100660335226903+c.lower,100660715969689+c.upper)) = pointBounds21013 := by
 decide +kernel
def cuts21014 : List PrefixCut := [⟨39,183581744,183581851⟩,
⟨124,590431903,590432244⟩,
⟨128,608697511,608697863⟩]
theorem checked21014 : checkPrefixCuts (2^48) 2758279169 9 Manual.Count131072.C021014.packed 128 cuts21014 = true := by
 decide +kernel
def pointBounds21014 : List (Nat × Nat × Nat) := [(2758319104,100661137229917,100661517973171),(2758406144,100661544080076,100661924823564)]
theorem point_links_checked21014 : (cuts21014.take 2).map (fun c => (2758279169-1+2*2^9*c.k,100660953648173+c.lower,100661334391320+c.upper)) = pointBounds21014 := by
 decide +kernel
def cuts21015 : List PrefixCut := [⟨81,386734990,386735217⟩,
⟨128,613056318,613056677⟩]
theorem checked21015 : checkPrefixCuts (2^48) 2758410241 9 Manual.Count131072.C021015.packed 128 cuts21015 = true := by
 decide +kernel
def pointBounds21015 : List (Nat × Nat × Nat) := [(2758493184,100661949080674,100662329824400)]
theorem point_links_checked21015 : (cuts21015.take 1).map (fun c => (2758410241-1+2*2^9*c.k,100661562345684+c.lower,100661943089183+c.upper)) = pointBounds21015 := by
 decide +kernel
def cuts21016 : List PrefixCut := [⟨38,184074521,184074626⟩,
⟨123,585070240,585070573⟩,
⟨128,607109332,607109677⟩]
theorem checked21016 : checkPrefixCuts (2^48) 2758541313 9 Manual.Count131072.C021016.packed 128 cuts21016 = true := by
 decide +kernel
def pointBounds21016 : List (Nat × Nat × Nat) := [(2758580224,100662359476523,100662740220486),(2758667264,100662760472242,100663141216433)]
theorem point_links_checked21016 : (cuts21016.take 2).map (fun c => (2758541313-1+2*2^9*c.k,100662175402002+c.lower,100662556145860+c.upper)) = pointBounds21016 := by
 decide +kernel
def cuts21017 : List PrefixCut := [⟨80,386290250,386290471⟩,
⟨128,620752428,620752785⟩]
theorem checked21017 : checkPrefixCuts (2^48) 2758672385 9 Manual.Count131072.C021017.packed 128 cuts21017 = true := by
 decide +kernel
def pointBounds21017 : List (Nat × Nat × Nat) := [(2758754304,100663168801584,100663549546008)]
theorem point_links_checked21017 : (cuts21017.take 1).map (fun c => (2758672385-1+2*2^9*c.k,100662782511334+c.lower,100663163255537+c.upper)) = pointBounds21017 := by
 decide +kernel
def cuts21018 : List PrefixCut := [⟨37,180486100,180486203⟩,
⟨122,586851237,586851580⟩,
⟨128,614499514,614499871⟩]
theorem checked21018 : checkPrefixCuts (2^48) 2758803457 9 Manual.Count131072.C021018.packed 128 cuts21018 = true := by
 decide +kernel
def pointBounds21018 : List (Nat × Nat × Nat) := [(2758841344,100663583749862,100663964494525),(2758928384,100663990114999,100664370859902)]
theorem point_links_checked21018 : (cuts21018.take 2).map (fun c => (2758803457-1+2*2^9*c.k,100663403263762+c.lower,100663784008322+c.upper)) = pointBounds21018 := by
 decide +kernel
def cuts21019 : List PrefixCut := [⟨79,376561467,376561683⟩,
⟨128,611205461,611205816⟩]
theorem checked21019 : checkPrefixCuts (2^48) 2758934529 9 Manual.Count131072.C021019.packed 128 cuts21019 = true := by
 decide +kernel
def pointBounds21019 : List (Nat × Nat × Nat) := [(2759015424,100664394324743,100664775069876)]
theorem point_links_checked21019 : (cuts21019.take 1).map (fun c => (2758934529-1+2*2^9*c.k,100664017763276+c.lower,100664398508193+c.upper)) = pointBounds21019 := by
 decide +kernel
def cuts21020 : List PrefixCut := [⟨36,172205570,172205672⟩,
⟨121,584041008,584041346⟩,
⟨128,617909484,617909842⟩]
theorem checked21020 : checkPrefixCuts (2^48) 2759065601 9 Manual.Count131072.C021020.packed 128 cuts21020 = true := by
 decide +kernel
def pointBounds21020 : List (Nat × Nat × Nat) := [(2759102464,100664801174307,100665181919681),(2759189504,100665213009745,100665593755355)]
theorem point_links_checked21020 : (cuts21020.take 2).map (fun c => (2759065601-1+2*2^9*c.k,100664628968737+c.lower,100665009714009+c.upper)) = pointBounds21020 := by
 decide +kernel
def cuts21021 : List PrefixCut := [⟨78,371425243,371425463⟩,
⟨128,612065533,612065890⟩]
theorem checked21021 : checkPrefixCuts (2^48) 2759196673 9 Manual.Count131072.C021021.packed 128 cuts21021 = true := by
 decide +kernel
def pointBounds21021 : List (Nat × Nat × Nat) := [(2759276544,100665618303464,100665999049314)]
theorem point_links_checked21021 : (cuts21021.take 1).map (fun c => (2759196673-1+2*2^9*c.k,100665246878221+c.lower,100665627623851+c.upper)) = pointBounds21021 := by
 decide +kernel
def cuts21022 : List PrefixCut := [⟨35,165864751,165864844⟩,
⟨120,567868655,567868981⟩,
⟨128,605304053,605304400⟩]
theorem checked21022 : checkPrefixCuts (2^48) 2759327745 9 Manual.Count131072.C021022.packed 128 cuts21022 = true := by
 decide +kernel
def pointBounds21022 : List (Nat × Nat × Nat) := [(2759363584,100666024808505,100666405554585),(2759450624,100666426812409,100666807558722)]
theorem point_links_checked21022 : (cuts21022.take 2).map (fun c => (2759327745-1+2*2^9*c.k,100665858943754+c.lower,100666239689741+c.upper)) = pointBounds21022 := by
 decide +kernel
def cuts21023 : List PrefixCut := [⟨77,371185992,371186213⟩,
⟨128,619249459,619249821⟩]
theorem checked21023 : checkPrefixCuts (2^48) 2759458817 9 Manual.Count131072.C021023.packed 128 cuts21023 = true := by
 decide +kernel
def pointBounds21023 : List (Nat × Nat × Nat) := [(2759537664,100666835433799,100667216180354)]
theorem point_links_checked21023 : (cuts21023.take 1).map (fun c => (2759458817-1+2*2^9*c.k,100666464247807+c.lower,100666844994141+c.upper)) = pointBounds21023 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000031
