import PlattAssemblyKernel
import PlattCertificates.Count131072.C018704
import PlattCertificates.Count131072.C018705
import PlattCertificates.Count131072.C018706
import PlattCertificates.Count131072.C018707
import PlattCertificates.Count131072.C018708
import PlattCertificates.Count131072.C018709
import PlattCertificates.Count131072.C018710
import PlattCertificates.Count131072.C018711
import PlattCertificates.Count131072.C018712
import PlattCertificates.Count131072.C018713
import PlattCertificates.Count131072.C018714
import PlattCertificates.Count131072.C018715
import PlattCertificates.Count131072.C018716
import PlattCertificates.Count131072.C018717
import PlattCertificates.Count131072.C018718
import PlattCertificates.Count131072.C018719
import PlattCertificates.Count131072.C018720
import PlattCertificates.Count131072.C018721
import PlattCertificates.Count131072.C018722
import PlattCertificates.Count131072.C018723
import PlattCertificates.Count131072.C018724
import PlattCertificates.Count131072.C018725
import PlattCertificates.Count131072.C018726
import PlattCertificates.Count131072.C018727
import PlattCertificates.Count131072.C018728
import PlattCertificates.Count131072.C018729
import PlattCertificates.Count131072.C018730
import PlattCertificates.Count131072.C018731
import PlattCertificates.Count131072.C018732
import PlattCertificates.Count131072.C018733
import PlattCertificates.Count131072.C018734
import PlattCertificates.Count131072.C018735
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000272
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts18704 : List PrefixCut := [⟨65,349158986,349159202⟩,
⟨128,692691944,692692367⟩]
theorem checked18704 : checkPrefixCuts (2^48) 2455502849 9 Manual.Count131072.C018704.packed 128 cuts18704 = true := by
 decide +kernel
def pointBounds18704 : List (Nat × Nat × Nat) := [(2455569408,99151641557467,99152021410461)]
theorem point_links_checked18704 : (cuts18704.take 1).map (fun c => (2455502849-1+2*2^9*c.k,99151292398481+c.lower,99151672251259+c.upper)) = pointBounds18704 := by
 decide +kernel
def cuts18705 : List PrefixCut := [⟨12,66940320,66940361⟩,
⟨87,476942376,476942665⟩,
⟨128,700334757,700335179⟩]
theorem checked18705 : checkPrefixCuts (2^48) 2455633921 9 Manual.Count131072.C018705.packed 128 cuts18705 = true := by
 decide +kernel
def pointBounds18705 : List (Nat × Nat × Nat) := [(2455646208,99152052030745,99152431883987),(2455723008,99152462032801,99152841886291)]
theorem point_links_checked18705 : (cuts18705.take 2).map (fun c => (2455633921-1+2*2^9*c.k,99151985090425+c.lower,99152364943626+c.upper)) = pointBounds18705 := by
 decide +kernel
def cuts18706 : List PrefixCut := [⟨34,182355951,182356063⟩,
⟨109,595656216,595656577⟩,
⟨128,695827400,695827822⟩]
theorem checked18706 : checkPrefixCuts (2^48) 2455764993 9 Manual.Count131072.C018706.packed 128 cuts18706 = true := by
 decide +kernel
def pointBounds18706 : List (Nat × Nat × Nat) := [(2455799808,99152867781133,99153247634868),(2455876608,99153281081398,99153660935382)]
theorem point_links_checked18706 : (cuts18706.take 2).map (fun c => (2455764993-1+2*2^9*c.k,99152685425182+c.lower,99153065278805+c.upper)) = pointBounds18706 := by
 decide +kernel
def cuts18707 : List PrefixCut := [⟨56,302915653,302915834⟩,
⟨128,694873314,694873729⟩]
theorem checked18707 : checkPrefixCuts (2^48) 2455896065 9 Manual.Count131072.C018707.packed 128 cuts18707 = true := by
 decide +kernel
def pointBounds18707 : List (Nat × Nat × Nat) := [(2455953408,99153684168235,99154064022461)]
theorem point_links_checked18707 : (cuts18707.take 1).map (fun c => (2455896065-1+2*2^9*c.k,99153381252582+c.lower,99153761106627+c.upper)) = pointBounds18707 := by
 decide +kernel
def cuts18708 : List PrefixCut := [⟨3,15242558,15242567⟩,
⟨78,434119599,434119862⟩,
⟨128,701941784,701942209⟩]
theorem checked18708 : checkPrefixCuts (2^48) 2456027137 9 Manual.Count131072.C018708.packed 128 cuts18708 = true := by
 decide +kernel
def pointBounds18708 : List (Nat × Nat × Nat) := [(2456030208,99154091368454,99154471222923),(2456107008,99154510245495,99154890100218)]
theorem point_links_checked18708 : (cuts18708.take 2).map (fun c => (2456027137-1+2*2^9*c.k,99154076125896+c.lower,99154455980356+c.upper)) = pointBounds18708 := by
 decide +kernel
def cuts18709 : List PrefixCut := [⟨25,133278705,133278787⟩,
⟨100,533450329,533450657⟩,
⟨128,687235761,687236179⟩]
theorem checked18709 : checkPrefixCuts (2^48) 2456158209 9 Manual.Count131072.C018709.packed 128 cuts18709 = true := by
 decide +kernel
def pointBounds18709 : List (Nat × Nat × Nat) := [(2456183808,99154911346385,99155291201352),(2456260608,99155311518009,99155691373222)]
theorem point_links_checked18709 : (cuts18709.take 2).map (fun c => (2456158209-1+2*2^9*c.k,99154778067680+c.lower,99155157922565+c.upper)) = pointBounds18709 := by
 decide +kernel
def cuts18710 : List PrefixCut := [⟨47,258864260,258864414⟩,
⟨122,663594309,663594707⟩,
⟨128,694876719,694877135⟩]
theorem checked18710 : checkPrefixCuts (2^48) 2456289281 9 Manual.Count131072.C018710.packed 128 cuts18710 = true := by
 decide +kernel
def pointBounds18710 : List (Nat × Nat × Nat) := [(2456337408,99155724167701,99156104023158),(2456414208,99156128897750,99156508753451)]
theorem point_links_checked18710 : (cuts18710.take 2).map (fun c => (2456289281-1+2*2^9*c.k,99155465303441+c.lower,99155845158744+c.upper)) = pointBounds18710 := by
 decide +kernel
def cuts18711 : List PrefixCut := [⟨69,372174635,372174861⟩,
⟨128,697589523,697589948⟩]
theorem checked18711 : checkPrefixCuts (2^48) 2456420353 9 Manual.Count131072.C018711.packed 128 cuts18711 = true := by
 decide +kernel
def pointBounds18711 : List (Nat × Nat × Nat) := [(2456491008,99156532354795,99156912210740)]
theorem point_links_checked18711 : (cuts18711.take 1).map (fun c => (2456420353-1+2*2^9*c.k,99156160180160+c.lower,99156540035879+c.upper)) = pointBounds18711 := by
 decide +kernel
def cuts18712 : List PrefixCut := [⟨16,83414919,83414967⟩,
⟨91,486044640,486044928⟩,
⟨128,683230093,683230501⟩]
theorem checked18712 : checkPrefixCuts (2^48) 2456551425 9 Manual.Count131072.C018712.packed 128 cuts18712 = true := by
 decide +kernel
def pointBounds18712 : List (Nat × Nat × Nat) := [(2456567808,99156941184602,99157321040794),(2456644608,99157343814323,99157723670755)]
theorem point_links_checked18712 : (cuts18712.take 2).map (fun c => (2456551425-1+2*2^9*c.k,99156857769683+c.lower,99157237625827+c.upper)) = pointBounds18712 := by
 decide +kernel
def cuts18713 : List PrefixCut := [⟨38,208754369,208754492⟩,
⟨113,608036359,608036727⟩,
⟨128,690411800,690412217⟩]
theorem checked18713 : checkPrefixCuts (2^48) 2456682497 9 Manual.Count131072.C018713.packed 128 cuts18713 = true := by
 decide +kernel
def pointBounds18713 : List (Nat × Nat × Nat) := [(2456721408,99157749754145,99158129610820),(2456798208,99158149036135,99158528893055)]
theorem point_links_checked18713 : (cuts18713.take 2).map (fun c => (2456682497-1+2*2^9*c.k,99157540999776+c.lower,99157920856328+c.upper)) = pointBounds18713 := by
 decide +kernel
def cuts18714 : List PrefixCut := [⟨60,330527627,330527825⟩,
⟨128,703664459,703664883⟩]
theorem checked18714 : checkPrefixCuts (2^48) 2456813569 9 Manual.Count131072.C018714.packed 128 cuts18714 = true := by
 decide +kernel
def pointBounds18714 : List (Nat × Nat × Nat) := [(2456875008,99158561939203,99158941796370)]
theorem point_links_checked18714 : (cuts18714.take 1).map (fun c => (2456813569-1+2*2^9*c.k,99158231411576+c.lower,99158611268545+c.upper)) = pointBounds18714 := by
 decide +kernel
def cuts18715 : List PrefixCut := [⟨7,37576602,37576624⟩,
⟨82,448506335,448506602⟩,
⟨128,699159169,699159583⟩]
theorem checked18715 : checkPrefixCuts (2^48) 2456944641 9 Manual.Count131072.C018715.packed 128 cuts18715 = true := by
 decide +kernel
def pointBounds18715 : List (Nat × Nat × Nat) := [(2456951808,99158972652637,99159352510052),(2457028608,99159383582370,99159763440030)]
theorem point_links_checked18715 : (cuts18715.take 2).map (fun c => (2456944641-1+2*2^9*c.k,99158935076035+c.lower,99159314933428+c.upper)) = pointBounds18715 := by
 decide +kernel
def cuts18716 : List PrefixCut := [⟨29,157400181,157400275⟩,
⟨104,562805682,562806024⟩,
⟨128,692134123,692134542⟩]
theorem checked18716 : checkPrefixCuts (2^48) 2457075713 9 Manual.Count131072.C018716.packed 128 cuts18716 = true := by
 decide +kernel
def pointBounds18716 : List (Nat × Nat × Nat) := [(2457105408,99159791635385,99160171493286),(2457182208,99160197040886,99160576899035)]
theorem point_links_checked18716 : (cuts18716.take 2).map (fun c => (2457075713-1+2*2^9*c.k,99159634235204+c.lower,99160014093011+c.upper)) = pointBounds18716 := by
 decide +kernel
def cuts18717 : List PrefixCut := [⟨51,273429696,273429856⟩,
⟨126,684537264,684537668⟩,
⟨128,694617197,694617607⟩]
theorem checked18717 : checkPrefixCuts (2^48) 2457206785 9 Manual.Count131072.C018717.packed 128 cuts18717 = true := by
 decide +kernel
def pointBounds18717 : List (Nat × Nat × Nat) := [(2457259008,99160599799023,99160979657409),(2457335808,99161010906591,99161390765221)]
theorem point_links_checked18717 : (cuts18717.take 2).map (fun c => (2457206785-1+2*2^9*c.k,99160326369327+c.lower,99160706227553+c.upper)) = pointBounds18717 := by
 decide +kernel
def cuts18718 : List PrefixCut := [⟨73,392194908,392195141⟩,
⟨128,685073266,685073679⟩]
theorem checked18718 : checkPrefixCuts (2^48) 2457337857 9 Manual.Count131072.C018718.packed 128 cuts18718 = true := by
 decide +kernel
def pointBounds18718 : List (Nat × Nat × Nat) := [(2457412608,99161413181432,99161793040301)]
theorem point_links_checked18718 : (cuts18718.take 1).map (fun c => (2457337857-1+2*2^9*c.k,99161020986524+c.lower,99161400845160+c.upper)) = pointBounds18718 := by
 decide +kernel
def cuts18719 : List PrefixCut := [⟨20,113507217,113507282⟩,
⟨95,521140066,521140377⟩,
⟨128,704393212,704393629⟩]
theorem checked18719 : checkPrefixCuts (2^48) 2457468929 9 Manual.Count131072.C018719.packed 128 cuts18719 = true := by
 decide +kernel
def pointBounds18719 : List (Nat × Nat × Nat) := [(2457489408,99161819567007,99162199426121),(2457566208,99162227199856,99162607059216)]
theorem point_links_checked18719 : (cuts18719.take 2).map (fun c => (2457468929-1+2*2^9*c.k,99161706059790+c.lower,99162085918839+c.upper)) = pointBounds18719 := by
 decide +kernel
def cuts18720 : List PrefixCut := [⟨42,225626880,225627017⟩,
⟨118,637128145,637128532⟩,
⟨128,692100899,692101319⟩]
theorem checked18720 : checkPrefixCuts (2^48) 2457600001 9 Manual.Count131072.C018720.packed 128 cuts18720 = true := by
 decide +kernel
def pointBounds18720 : List (Nat × Nat × Nat) := [(2457643008,99162636079882,99163015939485),(2457720832,99163047581147,99163427441000)]
theorem point_links_checked18720 : (cuts18720.take 2).map (fun c => (2457600001-1+2*2^9*c.k,99162410453002+c.lower,99162790312468+c.upper)) = pointBounds18720 := by
 decide +kernel
def cuts18721 : List PrefixCut := [⟨66,355026717,355026931⟩,
⟨128,687712188,687712602⟩]
theorem checked18721 : checkPrefixCuts (2^48) 2457731073 9 Manual.Count131072.C018721.packed 128 cuts18721 = true := by
 decide +kernel
def pointBounds18721 : List (Nat × Nat × Nat) := [(2457798656,99163457580618,99163837440718)]
theorem point_links_checked18721 : (cuts18721.take 1).map (fun c => (2457731073-1+2*2^9*c.k,99163102553901+c.lower,99163482413787+c.upper)) = pointBounds18721 := by
 decide +kernel
def cuts18722 : List PrefixCut := [⟨14,73521760,73521805⟩,
⟨90,494145375,494145678⟩,
⟨128,699241740,699242169⟩]
theorem checked18722 : checkPrefixCuts (2^48) 2457862145 9 Manual.Count131072.C018722.packed 128 cuts18722 = true := by
 decide +kernel
def pointBounds18722 : List (Nat × Nat × Nat) := [(2457876480,99163863787849,99164243648194),(2457954304,99164284411464,99164664272067)]
theorem point_links_checked18722 : (cuts18722.take 2).map (fun c => (2457862145-1+2*2^9*c.k,99163790266089+c.lower,99164170126389+c.upper)) = pointBounds18722 := by
 decide +kernel
def cuts18723 : List PrefixCut := [⟨38,208414007,208414133⟩,
⟨114,618132515,618132888⟩,
⟨128,688326114,688326529⟩]
theorem checked18723 : checkPrefixCuts (2^48) 2457993217 9 Manual.Count131072.C018723.packed 128 cuts18723 = true := by
 decide +kernel
def pointBounds18723 : List (Nat × Nat × Nat) := [(2458032128,99164697921836,99165077782691),(2458109952,99165107640344,99165487501446)]
theorem point_links_checked18723 : (cuts18723.take 2).map (fun c => (2457993217-1+2*2^9*c.k,99164489507829+c.lower,99164869368558+c.upper)) = pointBounds18723 := by
 decide +kernel
def cuts18724 : List PrefixCut := [⟨62,346267685,346267894⟩,
⟨128,701342985,701343408⟩]
theorem checked18724 : checkPrefixCuts (2^48) 2458124289 9 Manual.Count131072.C018724.packed 128 cuts18724 = true := by
 decide +kernel
def pointBounds18724 : List (Nat × Nat × Nat) := [(2458187776,99165524101628,99165903962981)]
theorem point_links_checked18724 : (cuts18724.take 1).map (fun c => (2458124289-1+2*2^9*c.k,99165177833943+c.lower,99165557695087+c.upper)) = pointBounds18724 := by
 decide +kernel
def cuts18725 : List PrefixCut := [⟨10,54731789,54731822⟩,
⟨86,466128881,466129159⟩,
⟨128,689855626,689856039⟩]
theorem checked18725 : checkPrefixCuts (2^48) 2458255361 9 Manual.Count131072.C018725.packed 128 cuts18725 = true := by
 decide +kernel
def pointBounds18725 : List (Nat × Nat × Nat) := [(2458265600,99165933908717,99166313770317),(2458343424,99166345305809,99166725167654)]
theorem point_links_checked18725 : (cuts18725.take 2).map (fun c => (2458255361-1+2*2^9*c.k,99165879176928+c.lower,99166259038495+c.upper)) = pointBounds18725 := by
 decide +kernel
def cuts18726 : List PrefixCut := [⟨34,180215086,180215195⟩,
⟨110,586548519,586548875⟩,
⟨128,685124504,685124920⟩]
theorem checked18726 : checkPrefixCuts (2^48) 2458386433 9 Manual.Count131072.C018726.packed 128 cuts18726 = true := by
 decide +kernel
def pointBounds18726 : List (Nat × Nat × Nat) := [(2458421248,99166749247640,99167129109729),(2458499072,99167155581073,99167535443409)]
theorem point_links_checked18726 : (cuts18726.take 2).map (fun c => (2458386433-1+2*2^9*c.k,99166569032554+c.lower,99166948894534+c.upper)) = pointBounds18726 := by
 decide +kernel
def cuts18727 : List PrefixCut := [⟨58,320681752,320681946⟩,
⟨128,694132618,694133040⟩]
theorem checked18727 : checkPrefixCuts (2^48) 2458517505 9 Manual.Count131072.C018727.packed 128 cuts18727 = true := by
 decide +kernel
def pointBounds18727 : List (Nat × Nat × Nat) := [(2458576896,99167574838810,99167954701400)]
theorem point_links_checked18727 : (cuts18727.take 1).map (fun c => (2458517505-1+2*2^9*c.k,99167254157058+c.lower,99167634019454+c.upper)) = pointBounds18727 := by
 decide +kernel
def cuts18728 : List PrefixCut := [⟨6,33429165,33429183⟩,
⟨82,450370743,450371013⟩,
⟨128,699476144,699476566⟩]
theorem checked18728 : checkPrefixCuts (2^48) 2458648577 9 Manual.Count131072.C018728.packed 128 cuts18728 = true := by
 decide +kernel
def pointBounds18728 : List (Nat × Nat × Nat) := [(2458654720,99167981718841,99168361581677),(2458732544,99168398660419,99168778523507)]
theorem point_links_checked18728 : (cuts18728.take 2).map (fun c => (2458648577-1+2*2^9*c.k,99167948289676+c.lower,99168328152494+c.upper)) = pointBounds18728 := by
 decide +kernel
def cuts18729 : List PrefixCut := [⟨30,162785965,162786064⟩,
⟨106,577068347,577068697⟩,
⟨128,700240110,700240534⟩]
theorem checked18729 : checkPrefixCuts (2^48) 2458779649 9 Manual.Count131072.C018729.packed 128 cuts18729 = true := by
 decide +kernel
def pointBounds18729 : List (Nat × Nat × Nat) := [(2458810368,99168810551785,99169190415124),(2458888192,99169224834167,99169604697757)]
theorem point_links_checked18729 : (cuts18729.take 2).map (fun c => (2458779649-1+2*2^9*c.k,99168647765820+c.lower,99169027629060+c.upper)) = pointBounds18729 := by
 decide +kernel
def cuts18730 : List PrefixCut := [⟨54,292471089,292471263⟩,
⟨128,695051642,695052061⟩]
theorem checked18730 : checkPrefixCuts (2^48) 2458910721 9 Manual.Count131072.C018730.packed 128 cuts18730 = true := by
 decide +kernel
def pointBounds18730 : List (Nat × Nat × Nat) := [(2458966016,99169640477019,99170020340857)]
theorem point_links_checked18730 : (cuts18730.take 1).map (fun c => (2458910721-1+2*2^9*c.k,99169348005930+c.lower,99169727869594+c.upper)) = pointBounds18730 := by
 decide +kernel
def cuts18731 : List PrefixCut := [⟨2,10416336,10416343⟩,
⟨78,426948450,426948705⟩,
⟨128,695930268,695930685⟩]
theorem checked18731 : checkPrefixCuts (2^48) 2459041793 9 Manual.Count131072.C018731.packed 128 cuts18731 = true := by
 decide +kernel
def pointBounds18731 : List (Nat × Nat × Nat) := [(2459043840,99170053473908,99170433337998),(2459121664,99170470006022,99170849870360)]
theorem point_links_checked18731 : (cuts18731.take 2).map (fun c => (2459041793-1+2*2^9*c.k,99170043057572+c.lower,99170422921655+c.upper)) = pointBounds18731 := by
 decide +kernel
def cuts18732 : List PrefixCut := [⟨26,140783993,140784078⟩,
⟨102,549392337,549392665⟩,
⟨128,690399276,690399690⟩]
theorem checked18732 : checkPrefixCuts (2^48) 2459172865 9 Manual.Count131072.C018732.packed 128 cuts18732 = true := by
 decide +kernel
def pointBounds18732 : List (Nat × Nat × Nat) := [(2459199488,99170879771833,99171259636418),(2459277312,99171288380177,99171668245005)]
theorem point_links_checked18732 : (cuts18732.take 2).map (fun c => (2459172865-1+2*2^9*c.k,99170738987840+c.lower,99171118852340+c.upper)) = pointBounds18732 := by
 decide +kernel
def cuts18733 : List PrefixCut := [⟨50,270220865,270221027⟩,
⟨126,676857765,676858169⟩,
⟨128,686700209,686700619⟩]
theorem checked18733 : checkPrefixCuts (2^48) 2459303937 9 Manual.Count131072.C018733.packed 128 cuts18733 = true := by
 decide +kernel
def pointBounds18733 : List (Nat × Nat × Nat) := [(2459355136,99171699607981,99172079473057),(2459432960,99172106244881,99172486110199)]
theorem point_links_checked18733 : (cuts18733.take 2).map (fun c => (2459303937-1+2*2^9*c.k,99171429387116+c.lower,99171809252030+c.upper)) = pointBounds18733 := by
 decide +kernel
def cuts18734 : List PrefixCut := [⟨74,406967169,406967413⟩,
⟨128,696734759,696735178⟩]
theorem checked18734 : checkPrefixCuts (2^48) 2459435009 9 Manual.Count131072.C018734.packed 128 cuts18734 = true := by
 decide +kernel
def pointBounds18734 : List (Nat × Nat × Nat) := [(2459510784,99172523054494,99172902920062)]
theorem point_links_checked18734 : (cuts18734.take 1).map (fun c => (2459435009-1+2*2^9*c.k,99172116087325+c.lower,99172495952649+c.upper)) = pointBounds18734 := by
 decide +kernel
def cuts18735 : List PrefixCut := [⟨22,116271391,116271461⟩,
⟨98,534199022,534199341⟩,
⟨128,695095320,695095739⟩]
theorem checked18735 : checkPrefixCuts (2^48) 2459566081 9 Manual.Count131072.C018735.packed 128 cuts18735 = true := by
 decide +kernel
def pointBounds18735 : List (Nat × Nat × Nat) := [(2459588608,99172929093475,99173308959288),(2459666432,99173347021106,99173726887168)]
theorem point_links_checked18735 : (cuts18735.take 2).map (fun c => (2459566081-1+2*2^9*c.k,99172812822084+c.lower,99173192687827+c.upper)) = pointBounds18735 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000272
