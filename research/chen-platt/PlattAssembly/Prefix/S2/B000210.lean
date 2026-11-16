import PlattAssemblyKernel
import PlattCertificates.Count131072.C016720
import PlattCertificates.Count131072.C016721
import PlattCertificates.Count131072.C016722
import PlattCertificates.Count131072.C016723
import PlattCertificates.Count131072.C016724
import PlattCertificates.Count131072.C016725
import PlattCertificates.Count131072.C016726
import PlattCertificates.Count131072.C016727
import PlattCertificates.Count131072.C016728
import PlattCertificates.Count131072.C016729
import PlattCertificates.Count131072.C016730
import PlattCertificates.Count131072.C016731
import PlattCertificates.Count131072.C016732
import PlattCertificates.Count131072.C016733
import PlattCertificates.Count131072.C016734
import PlattCertificates.Count131072.C016735
import PlattCertificates.Count131072.C016736
import PlattCertificates.Count131072.C016737
import PlattCertificates.Count131072.C016738
import PlattCertificates.Count131072.C016739
import PlattCertificates.Count131072.C016740
import PlattCertificates.Count131072.C016741
import PlattCertificates.Count131072.C016742
import PlattCertificates.Count131072.C016743
import PlattCertificates.Count131072.C016744
import PlattCertificates.Count131072.C016745
import PlattCertificates.Count131072.C016746
import PlattCertificates.Count131072.C016747
import PlattCertificates.Count131072.C016748
import PlattCertificates.Count131072.C016749
import PlattCertificates.Count131072.C016750
import PlattCertificates.Count131072.C016751
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000210
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts16720 : List PrefixCut := [⟨52,314362003,314362197⟩,
⟨120,729098119,729098575⟩,
⟨128,775763114,775763599⟩]
theorem checked16720 : checkPrefixCuts (2^48) 2195456001 9 Manual.Count131072.C016720.packed 128 cuts16720 = true := by
 decide +kernel
def pointBounds16720 : List (Nat × Nat × Nat) := [(2195509248,97690574887842,97690953842207),(2195578880,97690989623958,97691368578585)]
theorem point_links_checked16720 : (cuts16720.take 2).map (fun c => (2195456001-1+2*2^9*c.k,97690260525839+c.lower,97690639480010+c.upper)) = pointBounds16720 := by
 decide +kernel
def cuts16721 : List PrefixCut := [⟨60,356391857,356392083⟩,
⟨128,782639121,782639616⟩]
theorem checked16721 : checkPrefixCuts (2^48) 2195587073 9 Manual.Count131072.C016721.packed 128 cuts16721 = true := by
 decide +kernel
def pointBounds16721 : List (Nat × Nat × Nat) := [(2195648512,97691392680810,97691771635692),(2195718144,97691818928074,97692197883225)]
theorem point_links_checked16721 : (cuts16721.take 2).map (fun c => (2195587073-1+2*2^9*c.k,97691036288953+c.lower,97691415243609+c.upper)) = pointBounds16721 := by
 decide +kernel
def cuts16722 : List PrefixCut := [⟨68,422131668,422131933⟩,
⟨128,787335793,787336288⟩]
theorem checked16722 : checkPrefixCuts (2^48) 2195718145 9 Manual.Count131072.C016722.packed 128 cuts16722 = true := by
 decide +kernel
def pointBounds16722 : List (Nat × Nat × Nat) := [(2195787776,97692241059742,97692620015158)]
theorem point_links_checked16722 : (cuts16722.take 1).map (fun c => (2195718145-1+2*2^9*c.k,97691818928074+c.lower,97692197883225+c.upper)) = pointBounds16722 := by
 decide +kernel
def cuts16723 : List PrefixCut := [⟨8,48966572,48966603⟩,
⟨76,459022381,459022671⟩,
⟨128,781135931,781136423⟩]
theorem checked16723 : checkPrefixCuts (2^48) 2195849217 9 Manual.Count131072.C016723.packed 128 cuts16723 = true := by
 decide +kernel
def pointBounds16723 : List (Nat × Nat × Nat) := [(2195857408,97692655230439,97693034186116),(2195927040,97693065286248,97693444242184)]
theorem point_links_checked16723 : (cuts16723.take 2).map (fun c => (2195849217-1+2*2^9*c.k,97692606263867+c.lower,97692985219513+c.upper)) = pointBounds16723 := by
 decide +kernel
def cuts16724 : List PrefixCut := [⟨16,97158053,97158114⟩,
⟨84,505777850,505778169⟩,
⟨128,781217308,781217797⟩]
theorem checked16724 : checkPrefixCuts (2^48) 2195980289 9 Manual.Count131072.C016724.packed 128 cuts16724 = true := by
 decide +kernel
def pointBounds16724 : List (Nat × Nat × Nat) := [(2195996672,97693484557851,97693863514050),(2196066304,97693893177648,97694272134105)]
theorem point_links_checked16724 : (cuts16724.take 2).map (fun c => (2195980289-1+2*2^9*c.k,97693387399798+c.lower,97693766355936+c.upper)) = pointBounds16724 := by
 decide +kernel
def cuts16725 : List PrefixCut := [⟨24,146368945,146369039⟩,
⟨92,560217583,560217938⟩,
⟨128,782067889,782068384⟩]
theorem checked16725 : checkPrefixCuts (2^48) 2196111361 9 Manual.Count131072.C016725.packed 128 cuts16725 = true := by
 decide +kernel
def pointBounds16725 : List (Nat × Nat × Nat) := [(2196135936,97694314986051,97694693942772),(2196205568,97694728834689,97695107791671)]
theorem point_links_checked16725 : (cuts16725.take 2).map (fun c => (2196111361-1+2*2^9*c.k,97694168617106+c.lower,97694547573733+c.upper)) = pointBounds16725 := by
 decide +kernel
def cuts16726 : List PrefixCut := [⟨32,192626073,192626194⟩,
⟨100,611062251,611062636⟩,
⟨128,784712563,784713059⟩]
theorem checked16726 : checkPrefixCuts (2^48) 2196242433 9 Manual.Count131072.C016726.packed 128 cuts16726 = true := by
 decide +kernel
def pointBounds16726 : List (Nat × Nat × Nat) := [(2196275200,97695143311068,97695522268311),(2196344832,97695561747246,97695940704753)]
theorem point_links_checked16726 : (cuts16726.take 2).map (fun c => (2196242433-1+2*2^9*c.k,97694950684995+c.lower,97695329642117+c.upper)) = pointBounds16726 := by
 decide +kernel
def cuts16727 : List PrefixCut := [⟨40,241440583,241440736⟩,
⟨108,648316671,648317075⟩,
⟨128,770312913,770313394⟩]
theorem checked16727 : checkPrefixCuts (2^48) 2196373505 9 Manual.Count131072.C016727.packed 128 cuts16727 = true := by
 decide +kernel
def pointBounds16727 : List (Nat × Nat × Nat) := [(2196414464,97695976838141,97696355795912),(2196484096,97696383714229,97696762672251)]
theorem point_links_checked16727 : (cuts16727.take 2).map (fun c => (2196373505-1+2*2^9*c.k,97695735397558+c.lower,97696114355176+c.upper)) = pointBounds16727 := by
 decide +kernel
def cuts16728 : List PrefixCut := [⟨48,294349781,294349963⟩,
⟨116,708760427,708760868⟩,
⟨128,782056191,782056679⟩]
theorem checked16728 : checkPrefixCuts (2^48) 2196504577 9 Manual.Count131072.C016728.packed 128 cuts16728 = true := by
 decide +kernel
def pointBounds16728 : List (Nat × Nat × Nat) := [(2196553728,97696800060252,97697179018533),(2196623360,97697214470898,97697593429438)]
theorem point_links_checked16728 : (cuts16728.take 2).map (fun c => (2196504577-1+2*2^9*c.k,97696505710471+c.lower,97696884668570+c.upper)) = pointBounds16728 := by
 decide +kernel
def cuts16729 : List PrefixCut := [⟨56,342767558,342767771⟩,
⟨124,756126930,756127408⟩,
⟨128,781496981,781497474⟩]
theorem checked16729 : checkPrefixCuts (2^48) 2196635649 9 Manual.Count131072.C016729.packed 128 cuts16729 = true := by
 decide +kernel
def pointBounds16729 : List (Nat × Nat × Nat) := [(2196692992,97697630534220,97698009493020),(2196762624,97698043893592,97698422852657)]
theorem point_links_checked16729 : (cuts16729.take 2).map (fun c => (2196635649-1+2*2^9*c.k,97697287766662+c.lower,97697666725249+c.upper)) = pointBounds16729 := by
 decide +kernel
def cuts16730 : List PrefixCut := [⟨64,386054305,386054545⟩,
⟨128,782859516,782860007⟩]
theorem checked16730 : checkPrefixCuts (2^48) 2196766721 9 Manual.Count131072.C016730.packed 128 cuts16730 = true := by
 decide +kernel
def pointBounds16730 : List (Nat × Nat × Nat) := [(2196832256,97698455317948,97698834277268)]
theorem point_links_checked16730 : (cuts16730.take 1).map (fun c => (2196766721-1+2*2^9*c.k,97698069263643+c.lower,97698448222723+c.upper)) = pointBounds16730 := by
 decide +kernel
def cuts16731 : List PrefixCut := [⟨4,24215375,24215389⟩,
⟨72,440482322,440482603⟩,
⟨128,788450372,788450869⟩]
theorem checked16731 : checkPrefixCuts (2^48) 2196897793 9 Manual.Count131072.C016731.packed 128 cuts16731 = true := by
 decide +kernel
def pointBounds16731 : List (Nat × Nat × Nat) := [(2196901888,97698876338534,97699255298119),(2196971520,97699292605481,97699671565333)]
theorem point_links_checked16731 : (cuts16731.take 2).map (fun c => (2196897793-1+2*2^9*c.k,97698852123159+c.lower,97699231082730+c.upper)) = pointBounds16731 := by
 decide +kernel
def cuts16732 : List PrefixCut := [⟨12,70591807,70591854⟩,
⟨80,487472793,487473102⟩,
⟨128,777641832,777642325⟩]
theorem checked16732 : checkPrefixCuts (2^48) 2197028865 9 Manual.Count131072.C016732.packed 128 cuts16732 = true := by
 decide +kernel
def pointBounds16732 : List (Nat × Nat × Nat) := [(2197041152,97699711165338,97700090125453),(2197110784,97700128046324,97700507006701)]
theorem point_links_checked16732 : (cuts16732.take 2).map (fun c => (2197028865-1+2*2^9*c.k,97699640573531+c.lower,97700019533599+c.upper)) = pointBounds16732 := by
 decide +kernel
def cuts16733 : List PrefixCut := [⟨20,120549566,120549641⟩,
⟨88,527411951,527412284⟩,
⟨128,770549679,770550167⟩]
theorem checked16733 : checkPrefixCuts (2^48) 2197159937 9 Manual.Count131072.C016733.packed 128 cuts16733 = true := by
 decide +kernel
def pointBounds16733 : List (Nat × Nat × Nat) := [(2197180416,97700538764929,97700917725565),(2197250048,97700945627314,97701324588208)]
theorem point_links_checked16733 : (cuts16733.take 2).map (fun c => (2197159937-1+2*2^9*c.k,97700418215363+c.lower,97700797175924+c.upper)) = pointBounds16733 := by
 decide +kernel
def cuts16734 : List PrefixCut := [⟨28,168323469,168323574⟩,
⟨96,586432635,586432999⟩,
⟨128,780879610,780880097⟩]
theorem checked16734 : checkPrefixCuts (2^48) 2197291009 9 Manual.Count131072.C016734.packed 128 cuts16734 = true := by
 decide +kernel
def pointBounds16734 : List (Nat × Nat × Nat) := [(2197319680,97701357088511,97701736049665),(2197389312,97701775197677,97702154159090)]
theorem point_links_checked16734 : (cuts16734.take 2).map (fun c => (2197291009-1+2*2^9*c.k,97701188765042+c.lower,97701567726091+c.upper)) = pointBounds16734 := by
 decide +kernel
def cuts16735 : List PrefixCut := [⟨36,224033157,224033300⟩,
⟨104,638273228,638273631⟩,
⟨128,784803955,784804450⟩]
theorem checked16735 : checkPrefixCuts (2^48) 2197422081 9 Manual.Count131072.C016735.packed 128 cuts16735 = true := by
 decide +kernel
def pointBounds16735 : List (Nat × Nat × Nat) := [(2197458944,97702193677809,97702572639488),(2197528576,97702607917880,97702986879819)]
theorem point_links_checked16735 : (cuts16735.take 2).map (fun c => (2197422081-1+2*2^9*c.k,97701969644652+c.lower,97702348606188+c.upper)) = pointBounds16735 := by
 decide +kernel
def cuts16736 : List PrefixCut := [⟨44,267952319,267952490⟩,
⟨112,685496241,685496678⟩,
⟨128,785269325,785269826⟩]
theorem checked16736 : checkPrefixCuts (2^48) 2197553153 9 Manual.Count131072.C016736.packed 128 cuts16736 = true := by
 decide +kernel
def pointBounds16736 : List (Nat × Nat × Nat) := [(2197598208,97703022400926,97703401363128),(2197667840,97703439944848,97703818907316)]
theorem point_links_checked16736 : (cuts16736.take 2).map (fun c => (2197553153-1+2*2^9*c.k,97702754448607+c.lower,97703133410638+c.upper)) = pointBounds16736 := by
 decide +kernel
def cuts16737 : List PrefixCut := [⟨52,314939869,314940069⟩,
⟨120,728614962,728615425⟩,
⟨128,781123886,781124381⟩]
theorem checked16737 : checkPrefixCuts (2^48) 2197684225 9 Manual.Count131072.C016737.packed 128 cuts16737 = true := by
 decide +kernel
def pointBounds16737 : List (Nat × Nat × Nat) := [(2197737472,97703854657801,97704233620533),(2197807104,97704268332894,97704647295889)]
theorem point_links_checked16737 : (cuts16737.take 2).map (fun c => (2197684225-1+2*2^9*c.k,97703539717932+c.lower,97703918680464+c.upper)) = pointBounds16737 := by
 decide +kernel
def cuts16738 : List PrefixCut := [⟨60,364483042,364483272⟩,
⟨128,780949464,780949958⟩]
theorem checked16738 : checkPrefixCuts (2^48) 2197815297 9 Manual.Count131072.C016738.packed 128 cuts16738 = true := by
 decide +kernel
def pointBounds16738 : List (Nat × Nat × Nat) := [(2197876736,97704685324860,97705064288117),(2197946368,97705101791282,97705480754803)]
theorem point_links_checked16738 : (cuts16738.take 2).map (fun c => (2197815297-1+2*2^9*c.k,97704320841818+c.lower,97704699804845+c.upper)) = pointBounds16738 := by
 decide +kernel
def cuts16739 : List PrefixCut := [⟨68,418502204,418502466⟩,
⟨128,779366318,779366810⟩]
theorem checked16739 : checkPrefixCuts (2^48) 2197946369 9 Manual.Count131072.C016739.packed 128 cuts16739 = true := by
 decide +kernel
def pointBounds16739 : List (Nat × Nat × Nat) := [(2198016000,97705520293486,97705899257269)]
theorem point_links_checked16739 : (cuts16739.take 1).map (fun c => (2197946369-1+2*2^9*c.k,97705101791282+c.lower,97705480754803+c.upper)) = pointBounds16739 := by
 decide +kernel
def cuts16740 : List PrefixCut := [⟨8,48788879,48788911⟩,
⟨76,462654683,462654981⟩,
⟨128,777014874,777015373⟩]
theorem checked16740 : checkPrefixCuts (2^48) 2198077441 9 Manual.Count131072.C016740.packed 128 cuts16740 = true := by
 decide +kernel
def pointBounds16740 : List (Nat × Nat × Nat) := [(2198085632,97705929946479,97706308910524),(2198155264,97706343812283,97706722776594)]
theorem point_links_checked16740 : (cuts16740.take 2).map (fun c => (2198077441-1+2*2^9*c.k,97705881157600+c.lower,97706260121613+c.upper)) = pointBounds16740 := by
 decide +kernel
def cuts16741 : List PrefixCut := [⟨16,96931522,96931583⟩,
⟨84,513075850,513076169⟩,
⟨128,780041555,780042039⟩]
theorem checked16741 : checkPrefixCuts (2^48) 2198208513 9 Manual.Count131072.C016741.packed 128 cuts16741 = true := by
 decide +kernel
def pointBounds16741 : List (Nat × Nat × Nat) := [(2198224896,97706755103996,97707134068569),(2198294528,97707171248324,97707550213155)]
theorem point_links_checked16741 : (cuts16741.take 2).map (fun c => (2198208513-1+2*2^9*c.k,97706658172474+c.lower,97707037136986+c.upper)) = pointBounds16741 := by
 decide +kernel
def cuts16742 : List PrefixCut := [⟨24,146476695,146476784⟩,
⟨92,558881607,558881959⟩,
⟨128,777562321,777562812⟩]
theorem checked16742 : checkPrefixCuts (2^48) 2198339585 9 Manual.Count131072.C016742.packed 128 cuts16742 = true := by
 decide +kernel
def pointBounds16742 : List (Nat × Nat × Nat) := [(2198364160,97707584690724,97707963655809),(2198433792,97707997095636,97708376060984)]
theorem point_links_checked16742 : (cuts16742.take 2).map (fun c => (2198339585-1+2*2^9*c.k,97707438214029+c.lower,97707817179025+c.upper)) = pointBounds16742 := by
 decide +kernel
def cuts16743 : List PrefixCut := [⟨32,191662664,191662788⟩,
⟨100,605833933,605834316⟩,
⟨128,777899990,777900481⟩]
theorem checked16743 : checkPrefixCuts (2^48) 2198470657 9 Manual.Count131072.C016743.packed 128 cuts16743 = true := by
 decide +kernel
def pointBounds16743 : List (Nat × Nat × Nat) := [(2198503424,97708407439014,97708786404625),(2198573056,97708821610283,97709200576153)]
theorem point_links_checked16743 : (cuts16743.take 2).map (fun c => (2198470657-1+2*2^9*c.k,97708215776350+c.lower,97708594741837+c.upper)) = pointBounds16743 := by
 decide +kernel
def cuts16744 : List PrefixCut := [⟨40,244012404,244012555⟩,
⟨108,664430429,664430845⟩,
⟨128,787839260,787839753⟩]
theorem checked16744 : checkPrefixCuts (2^48) 2198601729 9 Manual.Count131072.C016744.packed 128 cuts16744 = true := by
 decide +kernel
def pointBounds16744 : List (Nat × Nat × Nat) := [(2198642688,97709237688744,97709616654873),(2198712320,97709658106769,97710037073163)]
theorem point_links_checked16744 : (cuts16744.take 2).map (fun c => (2198601729-1+2*2^9*c.k,97708993676340+c.lower,97709372642318+c.upper)) = pointBounds16744 := by
 decide +kernel
def cuts16745 : List PrefixCut := [⟨48,292003215,292003395⟩,
⟨116,702921629,702922074⟩,
⟨128,776783167,776783659⟩]
theorem checked16745 : checkPrefixCuts (2^48) 2198732801 9 Manual.Count131072.C016745.packed 128 cuts16745 = true := by
 decide +kernel
def pointBounds16745 : List (Nat × Nat × Nat) := [(2198781952,97710073518815,97710452485466),(2198851584,97710484437229,97710863404145)]
theorem point_links_checked16745 : (cuts16745.take 2).map (fun c => (2198732801-1+2*2^9*c.k,97709781515600+c.lower,97710160482071+c.upper)) = pointBounds16745 := by
 decide +kernel
def cuts16746 : List PrefixCut := [⟨56,336659910,336660117⟩,
⟨124,751776445,751776909⟩,
⟨128,774816756,774817235⟩]
theorem checked16746 : checkPrefixCuts (2^48) 2198863873 9 Manual.Count131072.C016746.packed 128 cuts16746 = true := by
 decide +kernel
def pointBounds16746 : List (Nat × Nat × Nat) := [(2198921216,97710894958677,97711273925847),(2198990848,97711310075212,97711689042639)]
theorem point_links_checked16746 : (cuts16746.take 2).map (fun c => (2198863873-1+2*2^9*c.k,97710558298767+c.lower,97710937265730+c.upper)) = pointBounds16746 := by
 decide +kernel
def cuts16747 : List PrefixCut := [⟨64,393343093,393343344⟩,
⟨128,780530649,780531144⟩]
theorem checked16747 : checkPrefixCuts (2^48) 2198994945 9 Manual.Count131072.C016747.packed 128 cuts16747 = true := by
 decide +kernel
def pointBounds16747 : List (Nat × Nat × Nat) := [(2199060480,97711726458616,97712105426309)]
theorem point_links_checked16747 : (cuts16747.take 1).map (fun c => (2198994945-1+2*2^9*c.k,97711333115523+c.lower,97711712082965+c.upper)) = pointBounds16747 := by
 decide +kernel
def cuts16748 : List PrefixCut := [⟨4,24446828,24446844⟩,
⟨72,445155612,445155896⟩,
⟨128,784963804,784964300⟩]
theorem checked16748 : checkPrefixCuts (2^48) 2199126017 9 Manual.Count131072.C016748.packed 128 cuts16748 = true := by
 decide +kernel
def pointBounds16748 : List (Nat × Nat × Nat) := [(2199130112,97712138093000,97712517060953),(2199199744,97712558801784,97712937770005)]
theorem point_links_checked16748 : (cuts16748.take 2).map (fun c => (2199126017-1+2*2^9*c.k,97712113646172+c.lower,97712492614109+c.upper)) = pointBounds16748 := by
 decide +kernel
def cuts16749 : List PrefixCut := [⟨12,71544174,71544221⟩,
⟨80,489026676,489026986⟩,
⟨128,781845234,781845729⟩]
theorem checked16749 : checkPrefixCuts (2^48) 2199257089 9 Manual.Count131072.C016749.packed 128 cuts16749 = true := by
 decide +kernel
def pointBounds16749 : List (Nat × Nat × Nat) := [(2199269376,97712970154150,97713349122630),(2199339008,97713387636652,97713766605395)]
theorem point_links_checked16749 : (cuts16749.take 2).map (fun c => (2199257089-1+2*2^9*c.k,97712898609976+c.lower,97713277578409+c.upper)) = pointBounds16749 := by
 decide +kernel
def cuts16750 : List PrefixCut := [⟨20,122475056,122475134⟩,
⟨88,536347866,536348200⟩,
⟨128,778087496,778087985⟩]
theorem checked16750 : checkPrefixCuts (2^48) 2199388161 9 Manual.Count131072.C016750.packed 128 cuts16750 = true := by
 decide +kernel
def pointBounds16750 : List (Nat × Nat × Nat) := [(2199408640,97713802930266,97714181899272),(2199478272,97714216803076,97714595772338)]
theorem point_links_checked16750 : (cuts16750.take 2).map (fun c => (2199388161-1+2*2^9*c.k,97713680455210+c.lower,97714059424138+c.upper)) = pointBounds16750 := by
 decide +kernel
def cuts16751 : List PrefixCut := [⟨28,167641047,167641156⟩,
⟨96,580975706,580976074⟩,
⟨128,771514750,771515239⟩]
theorem checked16751 : checkPrefixCuts (2^48) 2199519233 9 Manual.Count131072.C016751.packed 128 cuts16751 = true := by
 decide +kernel
def pointBounds16751 : List (Nat × Nat × Nat) := [(2199547904,97714626183753,97715005153279),(2199617536,97715039518412,97715418488197)]
theorem point_links_checked16751 : (cuts16751.take 2).map (fun c => (2199519233-1+2*2^9*c.k,97714458542706+c.lower,97714837512123+c.upper)) = pointBounds16751 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000210
