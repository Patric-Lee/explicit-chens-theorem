import PlattAssemblyKernel
import PlattCertificates.Count131072.C021056
import PlattCertificates.Count131072.C021057
import PlattCertificates.Count131072.C021058
import PlattCertificates.Count131072.C021059
import PlattCertificates.Count131072.C021060
import PlattCertificates.Count131072.C021061
import PlattCertificates.Count131072.C021062
import PlattCertificates.Count131072.C021063
import PlattCertificates.Count131072.C021064
import PlattCertificates.Count131072.C021065
import PlattCertificates.Count131072.C021066
import PlattCertificates.Count131072.C021067
import PlattCertificates.Count131072.C021068
import PlattCertificates.Count131072.C021069
import PlattCertificates.Count131072.C021070
import PlattCertificates.Count131072.C021071
import PlattCertificates.Count131072.C021072
import PlattCertificates.Count131072.C021073
import PlattCertificates.Count131072.C021074
import PlattCertificates.Count131072.C021075
import PlattCertificates.Count131072.C021076
import PlattCertificates.Count131072.C021077
import PlattCertificates.Count131072.C021078
import PlattCertificates.Count131072.C021079
import PlattCertificates.Count131072.C021080
import PlattCertificates.Count131072.C021081
import PlattCertificates.Count131072.C021082
import PlattCertificates.Count131072.C021083
import PlattCertificates.Count131072.C021084
import PlattCertificates.Count131072.C021085
import PlattCertificates.Count131072.C021086
import PlattCertificates.Count131072.C021087
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000033
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts21056 : List PrefixCut := [⟨18,85650538,85650587⟩,
⟨103,497905896,497906182⟩,
⟨128,617669347,617669705⟩]
theorem checked21056 : checkPrefixCuts (2^48) 2763784193 9 Manual.Count131072.C021056.packed 128 cuts21056 = true := by
 decide +kernel
def pointBounds21056 : List (Nat × Nat × Nat) := [(2763802624,100686823043299,100687203801452),(2763889664,100687235298657,100687616057047)]
theorem point_links_checked21056 : (cuts21056.take 2).map (fun c => (2763784193-1+2*2^9*c.k,100686737392761+c.lower,100687118150865+c.upper)) = pointBounds21056 := by
 decide +kernel
def cuts21057 : List PrefixCut := [⟨60,284433695,284433865⟩,
⟨128,609594905,609595261⟩]
theorem checked21057 : checkPrefixCuts (2^48) 2763915265 9 Manual.Count131072.C021057.packed 128 cuts21057 = true := by
 decide +kernel
def pointBounds21057 : List (Nat × Nat × Nat) := [(2763976704,100687639495803,100688020254435)]
theorem point_links_checked21057 : (cuts21057.take 1).map (fun c => (2763915265-1+2*2^9*c.k,100687355062108+c.lower,100687735820570+c.upper)) = pointBounds21057 := by
 decide +kernel
def cuts21058 : List PrefixCut := [⟨17,82994744,82994792⟩,
⟨102,486351705,486351984⟩,
⟨128,613842907,613843258⟩]
theorem checked21058 : checkPrefixCuts (2^48) 2764046337 9 Manual.Count131072.C021058.packed 128 cuts21058 = true := by
 decide +kernel
def pointBounds21058 : List (Nat × Nat × Nat) := [(2764063744,100688047651757,100688428410623),(2764150784,100688451008718,100688831767815)]
theorem point_links_checked21058 : (cuts21058.take 2).map (fun c => (2764046337-1+2*2^9*c.k,100687964657013+c.lower,100688345415831+c.upper)) = pointBounds21058 := by
 decide +kernel
def cuts21059 : List PrefixCut := [⟨59,272492884,272493046⟩,
⟨128,607907728,607908079⟩]
theorem checked21059 : checkPrefixCuts (2^48) 2764177409 9 Manual.Count131072.C021059.packed 128 cuts21059 = true := by
 decide +kernel
def pointBounds21059 : List (Nat × Nat × Nat) := [(2764237824,100688850992804,100689231752135)]
theorem point_links_checked21059 : (cuts21059.take 1).map (fun c => (2764177409-1+2*2^9*c.k,100688578499920+c.lower,100688959259089+c.upper)) = pointBounds21059 := by
 decide +kernel
def cuts21060 : List PrefixCut := [⟨16,76368297,76368341⟩,
⟨101,486611179,486611461⟩,
⟨128,616126714,616127069⟩]
theorem checked21060 : checkPrefixCuts (2^48) 2764308481 9 Manual.Count131072.C021060.packed 128 cuts21060 = true := by
 decide +kernel
def pointBounds21060 : List (Nat × Nat × Nat) := [(2764324864,100689262775945,100689643535509),(2764411904,100689673018827,100690053778629)]
theorem point_links_checked21060 : (cuts21060.take 2).map (fun c => (2764308481-1+2*2^9*c.k,100689186407648+c.lower,100689567167168+c.upper)) = pointBounds21060 := by
 decide +kernel
def cuts21061 : List PrefixCut := [⟨58,279085314,279085471⟩,
⟨128,611515783,611516132⟩]
theorem checked21061 : checkPrefixCuts (2^48) 2764439553 9 Manual.Count131072.C021061.packed 128 cuts21061 = true := by
 decide +kernel
def pointBounds21061 : List (Nat × Nat × Nat) := [(2764498944,100690081619676,100690462379708)]
theorem point_links_checked21061 : (cuts21061.take 1).map (fun c => (2764439553-1+2*2^9*c.k,100689802534362+c.lower,100690183294237+c.upper)) = pointBounds21061 := by
 decide +kernel
def cuts21062 : List PrefixCut := [⟨15,74222971,74223017⟩,
⟨100,483612704,483612990⟩,
⟨128,619631872,619632238⟩]
theorem checked21062 : checkPrefixCuts (2^48) 2764570625 9 Manual.Count131072.C021062.packed 128 cuts21062 = true := by
 decide +kernel
def pointBounds21062 : List (Nat × Nat × Nat) := [(2764585984,100690488273116,100690869033386),(2764673024,100690897662849,100691278423359)]
theorem point_links_checked21062 : (cuts21062.take 2).map (fun c => (2764570625-1+2*2^9*c.k,100690414050145+c.lower,100690794810369+c.upper)) = pointBounds21062 := by
 decide +kernel
def cuts21063 : List PrefixCut := [⟨57,268877930,268878085⟩,
⟨128,607588962,607589307⟩]
theorem checked21063 : checkPrefixCuts (2^48) 2764701697 9 Manual.Count131072.C021063.packed 128 cuts21063 = true := by
 decide +kernel
def pointBounds21063 : List (Nat × Nat × Nat) := [(2764760064,100691302559947,100691683320692)]
theorem point_links_checked21063 : (cuts21063.take 1).map (fun c => (2764701697-1+2*2^9*c.k,100691033682017+c.lower,100691414442607+c.upper)) = pointBounds21063 := by
 decide +kernel
def cuts21064 : List PrefixCut := [⟨14,67191387,67191426⟩,
⟨99,472062950,472063222⟩,
⟨128,615297121,615297477⟩]
theorem checked21064 : checkPrefixCuts (2^48) 2764832769 9 Manual.Count131072.C021064.packed 128 cuts21064 = true := by
 decide +kernel
def pointBounds21064 : List (Nat × Nat × Nat) := [(2764847104,100691708462366,100692089223340),(2764934144,100692113333929,100692494095136)]
theorem point_links_checked21064 : (cuts21064.take 2).map (fun c => (2764832769-1+2*2^9*c.k,100691641270979+c.lower,100692022031914+c.upper)) = pointBounds21064 := by
 decide +kernel
def cuts21065 : List PrefixCut := [⟨56,268648871,268649032⟩,
⟨128,609669159,609669522⟩]
theorem checked21065 : checkPrefixCuts (2^48) 2764963841 9 Manual.Count131072.C021065.packed 128 cuts21065 = true := by
 decide +kernel
def pointBounds21065 : List (Nat × Nat × Nat) := [(2765021184,100692525216971,100692905978423)]
theorem point_links_checked21065 : (cuts21065.take 1).map (fun c => (2764963841-1+2*2^9*c.k,100692256568100+c.lower,100692637329391+c.upper)) = pointBounds21065 := by
 decide +kernel
def cuts21066 : List PrefixCut := [⟨13,61789870,61789905⟩,
⟨98,469778811,469779084⟩,
⟨128,610047474,610047826⟩]
theorem checked21066 : checkPrefixCuts (2^48) 2765094913 9 Manual.Count131072.C021066.packed 128 cuts21066 = true := by
 decide +kernel
def pointBounds21066 : List (Nat × Nat × Nat) := [(2765108224,100692928027129,100693308788818),(2765195264,100693336016070,100693716777997)]
theorem point_links_checked21066 : (cuts21066.take 2).map (fun c => (2765094913-1+2*2^9*c.k,100692866237259+c.lower,100693246998913+c.upper)) = pointBounds21066 := by
 decide +kernel
def cuts21067 : List PrefixCut := [⟨55,256001551,256001701⟩,
⟨128,611341642,611341992⟩]
theorem checked21067 : checkPrefixCuts (2^48) 2765225985 9 Manual.Count131072.C021067.packed 128 cuts21067 = true := by
 decide +kernel
def pointBounds21067 : List (Nat × Nat × Nat) := [(2765282304,100693732286284,100694113048440)]
theorem point_links_checked21067 : (cuts21067.take 1).map (fun c => (2765225985-1+2*2^9*c.k,100693476284733+c.lower,100693857046739+c.upper)) = pointBounds21067 := by
 decide +kernel
def cuts21068 : List PrefixCut := [⟨12,59239377,59239411⟩,
⟨97,464136295,464136563⟩,
⟨128,617725109,617725465⟩]
theorem checked21068 : checkPrefixCuts (2^48) 2765357057 9 Manual.Count131072.C021068.packed 128 cuts21068 = true := by
 decide +kernel
def pointBounds21068 : List (Nat × Nat × Nat) := [(2765369344,100694146865752,100694527628142),(2765456384,100694551762670,100694932525294)]
theorem point_links_checked21068 : (cuts21068.take 2).map (fun c => (2765357057-1+2*2^9*c.k,100694087626375+c.lower,100694468388731+c.upper)) = pointBounds21068 := by
 decide +kernel
def cuts21069 : List PrefixCut := [⟨54,261066348,261066498⟩,
⟨128,614540761,614541115⟩]
theorem checked21069 : checkPrefixCuts (2^48) 2765488129 9 Manual.Count131072.C021069.packed 128 cuts21069 = true := by
 decide +kernel
def pointBounds21069 : List (Nat × Nat × Nat) := [(2765543424,100694966417832,100695347180694)]
theorem point_links_checked21069 : (cuts21069.take 1).map (fun c => (2765488129-1+2*2^9*c.k,100694705351484+c.lower,100695086114196+c.upper)) = pointBounds21069 := by
 decide +kernel
def cuts21070 : List PrefixCut := [⟨11,52516543,52516574⟩,
⟨96,454525537,454525811⟩,
⟨128,607692746,607693109⟩]
theorem checked21070 : checkPrefixCuts (2^48) 2765619201 9 Manual.Count131072.C021070.packed 128 cuts21070 = true := by
 decide +kernel
def pointBounds21070 : List (Nat × Nat × Nat) := [(2765630464,100695372408788,100695753171885),(2765717504,100695774417782,100696155181122)]
theorem point_links_checked21070 : (cuts21070.take 2).map (fun c => (2765619201-1+2*2^9*c.k,100695319892245+c.lower,100695700655311+c.upper)) = pointBounds21070 := by
 decide +kernel
def cuts21071 : List PrefixCut := [⟨53,255647802,255647954⟩,
⟨128,611327674,611328029⟩]
theorem checked21071 : checkPrefixCuts (2^48) 2765750273 9 Manual.Count131072.C021071.packed 128 cuts21071 = true := by
 decide +kernel
def pointBounds21071 : List (Nat × Nat × Nat) := [(2765804544,100696183232793,100696563996374)]
theorem point_links_checked21071 : (cuts21071.take 1).map (fun c => (2765750273-1+2*2^9*c.k,100695927584991+c.lower,100696308348420+c.upper)) = pointBounds21071 := by
 decide +kernel
def cuts21072 : List PrefixCut := [⟨10,47626777,47626803⟩,
⟨95,453668407,453668665⟩,
⟨128,615369190,615369541⟩]
theorem checked21072 : checkPrefixCuts (2^48) 2765881345 9 Manual.Count131072.C021072.packed 128 cuts21072 = true := by
 decide +kernel
def pointBounds21072 : List (Nat × Nat × Nat) := [(2765891584,100696586539442,100696967303252),(2765978624,100696992581072,100697373345114)]
theorem point_links_checked21072 : (cuts21072.take 2).map (fun c => (2765881345-1+2*2^9*c.k,100696538912665+c.lower,100696919676449+c.upper)) = pointBounds21072 := by
 decide +kernel
def cuts21073 : List PrefixCut := [⟨52,247075732,247075872⟩,
⟨128,610455695,610456042⟩]
theorem checked21073 : checkPrefixCuts (2^48) 2766012417 9 Manual.Count131072.C021073.packed 128 cuts21073 = true := by
 decide +kernel
def pointBounds21073 : List (Nat × Nat × Nat) := [(2766065664,100697401357587,100697782121862)]
theorem point_links_checked21073 : (cuts21073.take 1).map (fun c => (2766012417-1+2*2^9*c.k,100697154281855+c.lower,100697535045990+c.upper)) = pointBounds21073 := by
 decide +kernel
def cuts21074 : List PrefixCut := [⟨9,46604702,46604728⟩,
⟨94,452913325,452913589⟩,
⟨128,616939112,616939472⟩]
theorem checked21074 : checkPrefixCuts (2^48) 2766143489 9 Manual.Count131072.C021074.packed 128 cuts21074 = true := by
 decide +kernel
def pointBounds21074 : List (Nat × Nat × Nat) := [(2766152704,100697811342252,100698192106760),(2766239744,100698217650875,100698598415621)]
theorem point_links_checked21074 : (cuts21074.take 2).map (fun c => (2766143489-1+2*2^9*c.k,100697764737550+c.lower,100698145502032+c.upper)) = pointBounds21074 := by
 decide +kernel
def cuts21075 : List PrefixCut := [⟨51,245729574,245729716⟩,
⟨128,615586939,615587299⟩]
theorem checked21075 : checkPrefixCuts (2^48) 2766274561 9 Manual.Count131072.C021075.packed 128 cuts21075 = true := by
 decide +kernel
def pointBounds21075 : List (Nat × Nat × Nat) := [(2766326784,100698627406236,100699008171220)]
theorem point_links_checked21075 : (cuts21075.take 1).map (fun c => (2766274561-1+2*2^9*c.k,100698381676662+c.lower,100698762441504+c.upper)) = pointBounds21075 := by
 decide +kernel
def cuts21076 : List PrefixCut := [⟨8,36934295,36934316⟩,
⟨93,445035980,445036237⟩,
⟨128,607113132,607113486⟩]
theorem checked21076 : checkPrefixCuts (2^48) 2766405633 9 Manual.Count131072.C021076.packed 128 cuts21076 = true := by
 decide +kernel
def pointBounds21076 : List (Nat × Nat × Nat) := [(2766413824,100699034197896,100699414963119),(2766500864,100699442299581,100699823065040)]
theorem point_links_checked21076 : (cuts21076.take 2).map (fun c => (2766405633-1+2*2^9*c.k,100698997263601+c.lower,100699378028803+c.upper)) = pointBounds21076 := by
 decide +kernel
def cuts21077 : List PrefixCut := [⟨50,242247121,242247260⟩,
⟨128,617563596,617563949⟩]
theorem checked21077 : checkPrefixCuts (2^48) 2766536705 9 Manual.Count131072.C021077.packed 128 cuts21077 = true := by
 decide +kernel
def pointBounds21077 : List (Nat × Nat × Nat) := [(2766587904,100699846623854,100700227389549)]
theorem point_links_checked21077 : (cuts21077.take 1).map (fun c => (2766536705-1+2*2^9*c.k,100699604376733+c.lower,100699985142289+c.upper)) = pointBounds21077 := by
 decide +kernel
def cuts21078 : List PrefixCut := [⟨7,31742175,31742194⟩,
⟨92,439194921,439195168⟩,
⟨128,611531866,611532210⟩]
theorem checked21078 : checkPrefixCuts (2^48) 2766667777 9 Manual.Count131072.C021078.packed 128 cuts21078 = true := by
 decide +kernel
def pointBounds21078 : List (Nat × Nat × Nat) := [(2766674944,100700253682504,100700634448432),(2766761984,100700661135250,100701041901406)]
theorem point_links_checked21078 : (cuts21078.take 2).map (fun c => (2766667777-1+2*2^9*c.k,100700221940329+c.lower,100700602706238+c.upper)) = pointBounds21078 := by
 decide +kernel
def cuts21079 : List PrefixCut := [⟨49,235713368,235713502⟩,
⟨128,610587412,610587762⟩]
theorem checked21079 : checkPrefixCuts (2^48) 2766798849 9 Manual.Count131072.C021079.packed 128 cuts21079 = true := by
 decide +kernel
def pointBounds21079 : List (Nat × Nat × Nat) := [(2766849024,100701069185563,100701449951950)]
theorem point_links_checked21079 : (cuts21079.take 1).map (fun c => (2766798849-1+2*2^9*c.k,100700833472195+c.lower,100701214238448+c.upper)) = pointBounds21079 := by
 decide +kernel
def cuts21080 : List PrefixCut := [⟨6,29602883,29602900⟩,
⟨91,437525845,437526102⟩,
⟨128,616051662,616052025⟩]
theorem checked21080 : checkPrefixCuts (2^48) 2766929921 9 Manual.Count131072.C021080.packed 128 cuts21080 = true := by
 decide +kernel
def pointBounds21080 : List (Nat × Nat × Nat) := [(2766936064,100701473662490,100701854429110),(2767023104,100701881585452,100702262352312)]
theorem point_links_checked21080 : (cuts21080.take 2).map (fun c => (2766929921-1+2*2^9*c.k,100701444059607+c.lower,100701824826210+c.upper)) = pointBounds21080 := by
 decide +kernel
def cuts21081 : List PrefixCut := [⟨48,225620566,225620698⟩,
⟨128,608596795,608597150⟩]
theorem checked21081 : checkPrefixCuts (2^48) 2767060993 9 Manual.Count131072.C021081.packed 128 cuts21081 = true := by
 decide +kernel
def pointBounds21081 : List (Nat × Nat × Nat) := [(2767110144,100702285731835,100702666498933)]
theorem point_links_checked21081 : (cuts21081.take 1).map (fun c => (2767060993-1+2*2^9*c.k,100702060111269+c.lower,100702440878235+c.upper)) = pointBounds21081 := by
 decide +kernel
def cuts21082 : List PrefixCut := [⟨5,25327907,25327922⟩,
⟨90,437687879,437688133⟩,
⟨128,619553383,619553741⟩]
theorem checked21082 : checkPrefixCuts (2^48) 2767192065 9 Manual.Count131072.C021082.packed 128 cuts21082 = true := by
 decide +kernel
def pointBounds21082 : List (Nat × Nat × Nat) := [(2767197184,100702694035971,100703074803307),(2767284224,100703106395943,100703487163518)]
theorem point_links_checked21082 : (cuts21082.take 2).map (fun c => (2767192065-1+2*2^9*c.k,100702668708064+c.lower,100703049475385+c.upper)) = pointBounds21082 := by
 decide +kernel
def cuts21083 : List PrefixCut := [⟨47,227430037,227430167⟩,
⟨128,616065853,616066209⟩]
theorem checked21083 : checkPrefixCuts (2^48) 2767323137 9 Manual.Count131072.C021083.packed 128 cuts21083 = true := by
 decide +kernel
def pointBounds21083 : List (Nat × Nat × Nat) := [(2767371264,100703515691484,100703896459293)]
theorem point_links_checked21083 : (cuts21083.take 1).map (fun c => (2767323137-1+2*2^9*c.k,100703288261447+c.lower,100703669029126+c.upper)) = pointBounds21083 := by
 decide +kernel
def cuts21084 : List PrefixCut := [⟨4,18409308,18409320⟩,
⟨89,423204048,423204291⟩,
⟨128,612883651,612884006⟩]
theorem checked21084 : checkPrefixCuts (2^48) 2767454209 9 Manual.Count131072.C021084.packed 128 cuts21084 = true := by
 decide +kernel
def pointBounds21084 : List (Nat × Nat × Nat) := [(2767458304,100703922736608,100704303504655),(2767545344,100704327531348,100704708299626)]
theorem point_links_checked21084 : (cuts21084.take 2).map (fun c => (2767454209-1+2*2^9*c.k,100703904327300+c.lower,100704285095335+c.upper)) = pointBounds21084 := by
 decide +kernel
def cuts21085 : List PrefixCut := [⟨46,222119970,222120090⟩,
⟨128,612651312,612651660⟩]
theorem checked21085 : checkPrefixCuts (2^48) 2767585281 9 Manual.Count131072.C021085.packed 128 cuts21085 = true := by
 decide +kernel
def pointBounds21085 : List (Nat × Nat × Nat) := [(2767632384,100704739330921,100705120099431)]
theorem point_links_checked21085 : (cuts21085.take 1).map (fun c => (2767585281-1+2*2^9*c.k,100704517210951+c.lower,100704897979341+c.upper)) = pointBounds21085 := by
 decide +kernel
def cuts21086 : List PrefixCut := [⟨3,15559989,15559998⟩,
⟨88,417163765,417164007⟩,
⟨128,609672897,609673251⟩]
theorem checked21086 : checkPrefixCuts (2^48) 2767716353 9 Manual.Count131072.C021086.packed 128 cuts21086 = true := by
 decide +kernel
def pointBounds21086 : List (Nat × Nat × Nat) := [(2767719424,100705145422252,100705526190999),(2767806464,100705547026028,100705927795008)]
theorem point_links_checked21086 : (cuts21086.take 2).map (fun c => (2767716353-1+2*2^9*c.k,100705129862263+c.lower,100705510631001+c.upper)) = pointBounds21086 := by
 decide +kernel
def cuts21087 : List PrefixCut := [⟨45,216912593,216912718⟩,
⟨128,611983125,611983482⟩]
theorem checked21087 : checkPrefixCuts (2^48) 2767847425 9 Manual.Count131072.C021087.packed 128 cuts21087 = true := by
 decide +kernel
def pointBounds21087 : List (Nat × Nat × Nat) := [(2767893504,100705956447753,100706337216970)]
theorem point_links_checked21087 : (cuts21087.take 1).map (fun c => (2767847425-1+2*2^9*c.k,100705739535160+c.lower,100706120304252+c.upper)) = pointBounds21087 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000033
