import PlattAssemblyKernel
import PlattCertificates.Count131072.C016784
import PlattCertificates.Count131072.C016785
import PlattCertificates.Count131072.C016786
import PlattCertificates.Count131072.C016787
import PlattCertificates.Count131072.C016788
import PlattCertificates.Count131072.C016789
import PlattCertificates.Count131072.C016790
import PlattCertificates.Count131072.C016791
import PlattCertificates.Count131072.C016792
import PlattCertificates.Count131072.C016793
import PlattCertificates.Count131072.C016794
import PlattCertificates.Count131072.C016795
import PlattCertificates.Count131072.C016796
import PlattCertificates.Count131072.C016797
import PlattCertificates.Count131072.C016798
import PlattCertificates.Count131072.C016799
import PlattCertificates.Count131072.C016800
import PlattCertificates.Count131072.C016801
import PlattCertificates.Count131072.C016802
import PlattCertificates.Count131072.C016803
import PlattCertificates.Count131072.C016804
import PlattCertificates.Count131072.C016805
import PlattCertificates.Count131072.C016806
import PlattCertificates.Count131072.C016807
import PlattCertificates.Count131072.C016808
import PlattCertificates.Count131072.C016809
import PlattCertificates.Count131072.C016810
import PlattCertificates.Count131072.C016811
import PlattCertificates.Count131072.C016812
import PlattCertificates.Count131072.C016813
import PlattCertificates.Count131072.C016814
import PlattCertificates.Count131072.C016815
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000212
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts16784 : List PrefixCut := [⟨20,125803539,125803619⟩,
⟨88,540882890,540883228⟩,
⟨128,780345737,780346221⟩]
theorem checked16784 : checkPrefixCuts (2^48) 2203844609 9 Manual.Count131072.C016784.packed 128 cuts16784 = true := by
 decide +kernel
def pointBounds16784 : List (Nat × Nat × Nat) := [(2203865088,97740217489042,97740596474634),(2203934720,97740632568393,97741011554243)]
theorem point_links_checked16784 : (cuts16784.take 2).map (fun c => (2203844609-1+2*2^9*c.k,97740091685503+c.lower,97740470671015+c.upper)) = pointBounds16784 := by
 decide +kernel
def cuts16785 : List PrefixCut := [⟨28,161299623,161299724⟩,
⟨96,571627603,571627962⟩,
⟨128,767655838,767656320⟩]
theorem checked16785 : checkPrefixCuts (2^48) 2203975681 9 Manual.Count131072.C016785.packed 128 cuts16785 = true := by
 decide +kernel
def pointBounds16785 : List (Nat × Nat × Nat) := [(2204004352,97741033330863,97741412316960),(2204073984,97741443658843,97741822645198)]
theorem point_links_checked16785 : (cuts16785.take 2).map (fun c => (2203975681-1+2*2^9*c.k,97740872031240+c.lower,97741251017236+c.upper)) = pointBounds16785 := by
 decide +kernel
def cuts16786 : List PrefixCut := [⟨36,216457695,216457837⟩,
⟨104,635571036,635571441⟩,
⟨128,784211347,784211846⟩]
theorem checked16786 : checkPrefixCuts (2^48) 2204106753 9 Manual.Count131072.C016786.packed 128 cuts16786 = true := by
 decide +kernel
def pointBounds16786 : List (Nat × Nat × Nat) := [(2204143616,97741856144773,97742235131393),(2204213248,97742275258114,97742654244997)]
theorem point_links_checked16786 : (cuts16786.take 2).map (fun c => (2204106753-1+2*2^9*c.k,97741639687078+c.lower,97742018673556+c.upper)) = pointBounds16786 := by
 decide +kernel
def cuts16787 : List PrefixCut := [⟨44,263564249,263564415⟩,
⟨112,681374143,681374571⟩,
⟨128,779695463,779695953⟩]
theorem checked16787 : checkPrefixCuts (2^48) 2204237825 9 Manual.Count131072.C016787.packed 128 cuts16787 = true := by
 decide +kernel
def pointBounds16787 : List (Nat × Nat × Nat) := [(2204282880,97742687462674,97743066449817),(2204352512,97743105272568,97743484259973)]
theorem point_links_checked16787 : (cuts16787.take 2).map (fun c => (2204237825-1+2*2^9*c.k,97742423898425+c.lower,97742802885402+c.upper)) = pointBounds16787 := by
 decide +kernel
def cuts16788 : List PrefixCut := [⟨52,311941828,311942027⟩,
⟨120,723596421,723596873⟩,
⟨128,771221878,771222360⟩]
theorem checked16788 : checkPrefixCuts (2^48) 2204368897 9 Manual.Count131072.C016788.packed 128 cuts16788 = true := by
 decide +kernel
def pointBounds16788 : List (Nat × Nat × Nat) := [(2204422144,97743515535716,97743894523382),(2204491776,97743927190309,97744306178228)]
theorem point_links_checked16788 : (cuts16788.take 2).map (fun c => (2204368897-1+2*2^9*c.k,97743203593888+c.lower,97743582581355+c.upper)) = pointBounds16788 := by
 decide +kernel
def cuts16789 : List PrefixCut := [⟨60,365037659,365037889⟩,
⟨128,782411755,782412244⟩]
theorem checked16789 : checkPrefixCuts (2^48) 2204499969 9 Manual.Count131072.C016789.packed 128 cuts16789 = true := by
 decide +kernel
def pointBounds16789 : List (Nat × Nat × Nat) := [(2204561408,97744339853425,97744718841604),(2204631040,97744757227521,97745136215959)]
theorem point_links_checked16789 : (cuts16789.take 2).map (fun c => (2204499969-1+2*2^9*c.k,97743974815766+c.lower,97744353803715+c.upper)) = pointBounds16789 := by
 decide +kernel
def cuts16790 : List PrefixCut := [⟨68,409445268,409445530⟩,
⟨128,770364308,770364798⟩]
theorem checked16790 : checkPrefixCuts (2^48) 2204631041 9 Manual.Count131072.C016790.packed 128 cuts16790 = true := by
 decide +kernel
def pointBounds16790 : List (Nat × Nat × Nat) := [(2204700672,97745166672789,97745545661489)]
theorem point_links_checked16790 : (cuts16790.take 1).map (fun c => (2204631041-1+2*2^9*c.k,97744757227521+c.lower,97745136215959+c.upper)) = pointBounds16790 := by
 decide +kernel
def cuts16791 : List PrefixCut := [⟨8,49406953,49406987⟩,
⟨76,460358317,460358609⟩,
⟨128,773510135,773510626⟩]
theorem checked16791 : checkPrefixCuts (2^48) 2204762113 9 Manual.Count131072.C016791.packed 128 cuts16791 = true := by
 decide +kernel
def pointBounds16791 : List (Nat × Nat × Nat) := [(2204770304,97745576998782,97745955987744),(2204839936,97745987950146,97746366939366)]
theorem point_links_checked16791 : (cuts16791.take 2).map (fun c => (2204762113-1+2*2^9*c.k,97745527591829+c.lower,97745906580757+c.upper)) = pointBounds16791 := by
 decide +kernel
def cuts16792 : List PrefixCut := [⟨16,97786579,97786641⟩,
⟨84,511903426,511903744⟩,
⟨128,779974575,779975062⟩]
theorem checked16792 : checkPrefixCuts (2^48) 2204893185 9 Manual.Count131072.C016792.packed 128 cuts16792 = true := by
 decide +kernel
def pointBounds16792 : List (Nat × Nat × Nat) := [(2204909568,97746398888543,97746777878024),(2204979200,97746813005390,97747191995127)]
theorem point_links_checked16792 : (cuts16792.take 2).map (fun c => (2204893185-1+2*2^9*c.k,97746301101964+c.lower,97746680091383+c.upper)) = pointBounds16792 := by
 decide +kernel
def cuts16793 : List PrefixCut := [⟨24,142841355,142841445⟩,
⟨92,550294221,550294571⟩,
⟨128,767163189,767163678⟩]
theorem checked16793 : checkPrefixCuts (2^48) 2205024257 9 Manual.Count131072.C016793.packed 128 cuts16793 = true := by
 decide +kernel
def pointBounds16793 : List (Nat × Nat × Nat) := [(2205048832,97747223917894,97747602907890),(2205118464,97747631370760,97748010361016)]
theorem point_links_checked16793 : (cuts16793.take 2).map (fun c => (2205024257-1+2*2^9*c.k,97747081076539+c.lower,97747460066445+c.upper)) = pointBounds16793 := by
 decide +kernel
def cuts16794 : List PrefixCut := [⟨32,195804475,195804594⟩,
⟨100,612549412,612549794⟩,
⟨128,783200433,783200924⟩]
theorem checked16794 : checkPrefixCuts (2^48) 2205155329 9 Manual.Count131072.C016794.packed 128 cuts16794 = true := by
 decide +kernel
def pointBounds16794 : List (Nat × Nat × Nat) := [(2205188096,97748044044203,97748423034717),(2205257728,97748460789140,97748839779917)]
theorem point_links_checked16794 : (cuts16794.take 2).map (fun c => (2205155329-1+2*2^9*c.k,97747848239728+c.lower,97748227230123+c.upper)) = pointBounds16794 := by
 decide +kernel
def cuts16795 : List PrefixCut := [⟨40,246080760,246080916⟩,
⟨108,662161267,662161683⟩,
⟨128,784047387,784047879⟩]
theorem checked16795 : checkPrefixCuts (2^48) 2205286401 9 Manual.Count131072.C016795.packed 128 cuts16795 = true := by
 decide +kernel
def pointBounds16795 : List (Nat × Nat × Nat) := [(2205327360,97748877520921,97749256511963),(2205396992,97749293601428,97749672592730)]
theorem point_links_checked16795 : (cuts16795.take 2).map (fun c => (2205286401-1+2*2^9*c.k,97748631440161+c.lower,97749010431047+c.upper)) = pointBounds16795 := by
 decide +kernel
def cuts16796 : List PrefixCut := [⟨48,293160227,293160406⟩,
⟨116,709342045,709342482⟩,
⟨128,783617821,783618306⟩]
theorem checked16796 : checkPrefixCuts (2^48) 2205417473 9 Manual.Count131072.C016796.packed 128 cuts16796 = true := by
 decide +kernel
def pointBounds16796 : List (Nat × Nat × Nat) := [(2205466624,97749708647775,97750087639332),(2205536256,97750124829593,97750503821408)]
theorem point_links_checked16796 : (cuts16796.take 2).map (fun c => (2205417473-1+2*2^9*c.k,97749415487548+c.lower,97749794478926+c.upper)) = pointBounds16796 := by
 decide +kernel
def cuts16797 : List PrefixCut := [⟨56,337170968,337171182⟩,
⟨124,752560694,752561169⟩,
⟨128,777955840,777956331⟩]
theorem checked16797 : checkPrefixCuts (2^48) 2205548545 9 Manual.Count131072.C016797.packed 128 cuts16797 = true := by
 decide +kernel
def pointBounds16797 : List (Nat × Nat × Nat) := [(2205605888,97750536276337,97750915268414),(2205675520,97750951666063,97751330658401)]
theorem point_links_checked16797 : (cuts16797.take 2).map (fun c => (2205548545-1+2*2^9*c.k,97750199105369+c.lower,97750578097232+c.upper)) = pointBounds16797 := by
 decide +kernel
def cuts16798 : List PrefixCut := [⟨64,386791317,386791559⟩,
⟨128,776888978,776889461⟩]
theorem checked16798 : checkPrefixCuts (2^48) 2205679617 9 Manual.Count131072.C016798.packed 128 cuts16798 = true := by
 decide +kernel
def pointBounds16798 : List (Nat × Nat × Nat) := [(2205745152,97751363852526,97751742845122)]
theorem point_links_checked16798 : (cuts16798.take 1).map (fun c => (2205679617-1+2*2^9*c.k,97750977061209+c.lower,97751356053563+c.upper)) = pointBounds16798 := by
 decide +kernel
def cuts16799 : List PrefixCut := [⟨4,23096680,23096695⟩,
⟨72,438702378,438702654⟩,
⟨128,777608448,777608939⟩]
theorem checked16799 : checkPrefixCuts (2^48) 2205810689 9 Manual.Count131072.C016799.packed 128 cuts16799 = true := by
 decide +kernel
def pointBounds16799 : List (Nat × Nat × Nat) := [(2205814784,97751777046867,97752156039719),(2205884416,97752192652565,97752571645678)]
theorem point_links_checked16799 : (cuts16799.take 2).map (fun c => (2205810689-1+2*2^9*c.k,97751753950187+c.lower,97752132943024+c.upper)) = pointBounds16799 := by
 decide +kernel
def cuts16800 : List PrefixCut := [⟨12,71072171,71072215⟩,
⟨80,485630996,485631296⟩,
⟨128,776158756,776159235⟩]
theorem checked16800 : checkPrefixCuts (2^48) 2205941761 9 Manual.Count131072.C016800.packed 128 cuts16800 = true := by
 decide +kernel
def pointBounds16800 : List (Nat × Nat × Nat) := [(2205954048,97752602630806,97752981624178),(2206023680,97753017189631,97753396183259)]
theorem point_links_checked16800 : (cuts16800.take 2).map (fun c => (2205941761-1+2*2^9*c.k,97752531558635+c.lower,97752910551963+c.upper)) = pointBounds16800 := by
 decide +kernel
def cuts16801 : List PrefixCut := [⟨20,124783350,124783431⟩,
⟨88,544674567,544674909⟩,
⟨128,782364547,782365042⟩]
theorem checked16801 : checkPrefixCuts (2^48) 2206072833 9 Manual.Count131072.C016801.packed 128 cuts16801 = true := by
 decide +kernel
def pointBounds16801 : List (Nat × Nat × Nat) := [(2206093312,97753432500741,97753811494629),(2206162944,97753852391958,97754231386107)]
theorem point_links_checked16801 : (cuts16801.take 2).map (fun c => (2206072833-1+2*2^9*c.k,97753307717391+c.lower,97753686711198+c.upper)) = pointBounds16801 := by
 decide +kernel
def cuts16802 : List PrefixCut := [⟨28,170450245,170450354⟩,
⟨96,576919049,576919414⟩,
⟨128,770197754,770198241⟩]
theorem checked16802 : checkPrefixCuts (2^48) 2206203905 9 Manual.Count131072.C016802.packed 128 cuts16802 = true := by
 decide +kernel
def pointBounds16802 : List (Nat × Nat × Nat) := [(2206232576,97754260532183,97754639526594),(2206302208,97754667000987,97755045995654)]
theorem point_links_checked16802 : (cuts16802.take 2).map (fun c => (2206203905-1+2*2^9*c.k,97754090081938+c.lower,97754469076240+c.upper)) = pointBounds16802 := by
 decide +kernel
def cuts16803 : List PrefixCut := [⟨36,218025141,218025280⟩,
⟨104,634163786,634164190⟩,
⟨128,771555481,771555974⟩]
theorem checked16803 : checkPrefixCuts (2^48) 2206334977 9 Manual.Count131072.C016803.packed 128 cuts16803 = true := by
 decide +kernel
def pointBounds16803 : List (Nat × Nat × Nat) := [(2206371840,97755078304833,97755457299761),(2206441472,97755494443478,97755873438671)]
theorem point_links_checked16803 : (cuts16803.take 2).map (fun c => (2206334977-1+2*2^9*c.k,97754860279692+c.lower,97755239274481+c.upper)) = pointBounds16803 := by
 decide +kernel
def cuts16804 : List PrefixCut := [⟨44,269038586,269038750⟩,
⟨112,695738831,695739260⟩,
⟨128,792812821,792813310⟩]
theorem checked16804 : checkPrefixCuts (2^48) 2206466049 9 Manual.Count131072.C016804.packed 128 cuts16804 = true := by
 decide +kernel
def pointBounds16804 : List (Nat × Nat × Nat) := [(2206511104,97755900873759,97756279869205),(2206580736,97756327574004,97756706569715)]
theorem point_links_checked16804 : (cuts16804.take 2).map (fun c => (2206466049-1+2*2^9*c.k,97755631835173+c.lower,97756010830455+c.upper)) = pointBounds16804 := by
 decide +kernel
def cuts16805 : List PrefixCut := [⟨52,315836319,315836518⟩,
⟨120,727585550,727586007⟩,
⟨128,778224200,778224689⟩]
theorem checked16805 : checkPrefixCuts (2^48) 2206597121 9 Manual.Count131072.C016805.packed 128 cuts16805 = true := by
 decide +kernel
def pointBounds16805 : List (Nat × Nat × Nat) := [(2206650368,97756740484313,97757119480283),(2206720000,97757152233544,97757531229772)]
theorem point_links_checked16805 : (cuts16805.take 2).map (fun c => (2206597121-1+2*2^9*c.k,97756424647994+c.lower,97756803643765+c.upper)) = pointBounds16805 := by
 decide +kernel
def cuts16806 : List PrefixCut := [⟨60,359056797,359057023⟩,
⟨128,773331045,773331535⟩]
theorem checked16806 : checkPrefixCuts (2^48) 2206728193 9 Manual.Count131072.C016806.packed 128 cuts16806 = true := by
 decide +kernel
def pointBounds16806 : List (Nat × Nat × Nat) := [(2206789632,97757561928991,97757940925477),(2206859264,97757976203239,97758355199989)]
theorem point_links_checked16806 : (cuts16806.take 2).map (fun c => (2206728193-1+2*2^9*c.k,97757202872194+c.lower,97757581868454+c.upper)) = pointBounds16806 := by
 decide +kernel
def cuts16807 : List PrefixCut := [⟨68,416301887,416302148⟩,
⟨128,784381376,784381873⟩]
theorem checked16807 : checkPrefixCuts (2^48) 2206859265 9 Manual.Count131072.C016807.packed 128 cuts16807 = true := by
 decide +kernel
def pointBounds16807 : List (Nat × Nat × Nat) := [(2206928896,97758392505126,97758771502137)]
theorem point_links_checked16807 : (cuts16807.take 1).map (fun c => (2206859265-1+2*2^9*c.k,97757976203239+c.lower,97758355199989+c.upper)) = pointBounds16807 := by
 decide +kernel
def cuts16808 : List PrefixCut := [⟨8,49229535,49229567⟩,
⟨76,460148593,460148891⟩,
⟨128,770688617,770689106⟩]
theorem checked16808 : checkPrefixCuts (2^48) 2206990337 9 Manual.Count131072.C016808.packed 128 cuts16808 = true := by
 decide +kernel
def pointBounds16808 : List (Nat × Nat × Nat) := [(2206998528,97758809814150,97759188811429),(2207068160,97759220733208,97759599730753)]
theorem point_links_checked16808 : (cuts16808.take 2).map (fun c => (2206990337-1+2*2^9*c.k,97758760584615+c.lower,97759139581862+c.upper)) = pointBounds16808 := by
 decide +kernel
def cuts16809 : List PrefixCut := [⟨16,96667633,96667692⟩,
⟨84,508963547,508963866⟩,
⟨128,779952155,779952645⟩]
theorem checked16809 : checkPrefixCuts (2^48) 2207121409 9 Manual.Count131072.C016809.packed 128 cuts16809 = true := by
 decide +kernel
def pointBounds16809 : List (Nat × Nat × Nat) := [(2207137792,97759627940865,97760006938660),(2207207424,97760040236779,97760419234834)]
theorem point_links_checked16809 : (cuts16809.take 2).map (fun c => (2207121409-1+2*2^9*c.k,97759531273232+c.lower,97759910270968+c.upper)) = pointBounds16809 := by
 decide +kernel
def cuts16810 : List PrefixCut := [⟨24,142187068,142187157⟩,
⟨92,557262451,557262803⟩,
⟨128,772254830,772255313⟩]
theorem checked16810 : checkPrefixCuts (2^48) 2207252481 9 Manual.Count131072.C016810.packed 128 cuts16810 = true := by
 decide +kernel
def pointBounds16810 : List (Nat × Nat × Nat) := [(2207277056,97760453412455,97760832410770),(2207346688,97760868487838,97761247486416)]
theorem point_links_checked16810 : (cuts16810.take 2).map (fun c => (2207252481-1+2*2^9*c.k,97760311225387+c.lower,97760690223613+c.upper)) = pointBounds16810 := by
 decide +kernel
def cuts16811 : List PrefixCut := [⟨32,191653886,191654007⟩,
⟨100,614098655,614099037⟩,
⟨128,787127617,787128106⟩]
theorem checked16811 : checkPrefixCuts (2^48) 2207383553 9 Manual.Count131072.C016811.packed 128 cuts16811 = true := by
 decide +kernel
def pointBounds16811 : List (Nat × Nat × Nat) := [(2207416320,97761275134103,97761654132933),(2207485952,97761697578872,97762076577963)]
theorem point_links_checked16811 : (cuts16811.take 2).map (fun c => (2207383553-1+2*2^9*c.k,97761083480217+c.lower,97761462478926+c.upper)) = pointBounds16811 := by
 decide +kernel
def cuts16812 : List PrefixCut := [⟨40,245067334,245067487⟩,
⟨108,659452765,659453178⟩,
⟨128,783383368,783383858⟩]
theorem checked16812 : checkPrefixCuts (2^48) 2207514625 9 Manual.Count131072.C016812.packed 128 cuts16812 = true := by
 decide +kernel
def pointBounds16812 : List (Nat × Nat × Nat) := [(2207555584,97762115675168,97762494674519),(2207625216,97762530060599,97762909060210)]
theorem point_links_checked16812 : (cuts16812.take 2).map (fun c => (2207514625-1+2*2^9*c.k,97761870607834+c.lower,97762249607032+c.upper)) = pointBounds16812 := by
 decide +kernel
def cuts16813 : List PrefixCut := [⟨48,287764394,287764570⟩,
⟨116,700848721,700849160⟩,
⟨128,774794562,774795046⟩]
theorem checked16813 : checkPrefixCuts (2^48) 2207645697 9 Manual.Count131072.C016813.packed 128 cuts16813 = true := by
 decide +kernel
def pointBounds16813 : List (Nat × Nat × Nat) := [(2207694848,97762941755596,97763320755460),(2207764480,97763354839923,97763733840050)]
theorem point_links_checked16813 : (cuts16813.take 2).map (fun c => (2207645697-1+2*2^9*c.k,97762653991202+c.lower,97763032990890+c.upper)) = pointBounds16813 := by
 decide +kernel
def cuts16814 : List PrefixCut := [⟨56,338743063,338743278⟩,
⟨124,747466871,747467344⟩,
⟨128,771689023,771689512⟩]
theorem checked16814 : checkPrefixCuts (2^48) 2207776769 9 Manual.Count131072.C016814.packed 128 cuts16814 = true := by
 decide +kernel
def pointBounds16814 : List (Nat × Nat × Nat) := [(2207834112,97763767528827,97764146529214),(2207903744,97764176252635,97764555253280)]
theorem point_links_checked16814 : (cuts16814.take 2).map (fun c => (2207776769-1+2*2^9*c.k,97763428785764+c.lower,97763807785936+c.upper)) = pointBounds16814 := by
 decide +kernel
def cuts16815 : List PrefixCut := [⟨64,393795034,393795275⟩,
⟨128,781841764,781842247⟩]
theorem checked16815 : checkPrefixCuts (2^48) 2207907841 9 Manual.Count131072.C016815.packed 128 cuts16815 = true := by
 decide +kernel
def pointBounds16815 : List (Nat × Nat × Nat) := [(2207973376,97764594269821,97764973270723)]
theorem point_links_checked16815 : (cuts16815.take 1).map (fun c => (2207907841-1+2*2^9*c.k,97764200474787+c.lower,97764579475448+c.upper)) = pointBounds16815 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000212
