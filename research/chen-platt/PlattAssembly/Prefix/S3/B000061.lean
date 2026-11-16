import PlattAssemblyKernel
import PlattCertificates.Count131072.C021952
import PlattCertificates.Count131072.C021953
import PlattCertificates.Count131072.C021954
import PlattCertificates.Count131072.C021955
import PlattCertificates.Count131072.C021956
import PlattCertificates.Count131072.C021957
import PlattCertificates.Count131072.C021958
import PlattCertificates.Count131072.C021959
import PlattCertificates.Count131072.C021960
import PlattCertificates.Count131072.C021961
import PlattCertificates.Count131072.C021962
import PlattCertificates.Count131072.C021963
import PlattCertificates.Count131072.C021964
import PlattCertificates.Count131072.C021965
import PlattCertificates.Count131072.C021966
import PlattCertificates.Count131072.C021967
import PlattCertificates.Count131072.C021968
import PlattCertificates.Count131072.C021969
import PlattCertificates.Count131072.C021970
import PlattCertificates.Count131072.C021971
import PlattCertificates.Count131072.C021972
import PlattCertificates.Count131072.C021973
import PlattCertificates.Count131072.C021974
import PlattCertificates.Count131072.C021975
import PlattCertificates.Count131072.C021976
import PlattCertificates.Count131072.C021977
import PlattCertificates.Count131072.C021978
import PlattCertificates.Count131072.C021979
import PlattCertificates.Count131072.C021980
import PlattCertificates.Count131072.C021981
import PlattCertificates.Count131072.C021982
import PlattCertificates.Count131072.C021983
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000061
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts21952 : List PrefixCut := [⟨74,340454937,340455134⟩,
⟨128,586827306,586827648⟩]
theorem checked21952 : checkPrefixCuts (2^48) 2881224705 9 Manual.Count131072.C021952.packed 128 cuts21952 = true := by
 decide +kernel
def pointBounds21952 : List (Nat × Nat × Nat) := [(2881300480,101225448498968,101225829567292)]
theorem point_links_checked21952 : (cuts21952.take 1).map (fun c => (2881224705-1+2*2^9*c.k,101225108044031+c.lower,101225489112158+c.upper)) = pointBounds21952 := by
 decide +kernel
def cuts21953 : List PrefixCut := [⟨34,157472676,157472763⟩,
⟨122,565310174,565310501⟩,
⟨128,594517696,594518038⟩]
theorem checked21953 : checkPrefixCuts (2^48) 2881355777 9 Manual.Count131072.C021953.packed 128 cuts21953 = true := by
 decide +kernel
def pointBounds21953 : List (Nat × Nat × Nat) := [(2881390592,101225852344013,101226233412569),(2881480704,101226260181511,101226641250307)]
theorem point_links_checked21953 : (cuts21953.take 2).map (fun c => (2881355777-1+2*2^9*c.k,101225694871337+c.lower,101226075939806+c.upper)) = pointBounds21953 := by
 decide +kernel
def cuts21954 : List PrefixCut := [⟨82,381840836,381841051⟩,
⟨128,597616531,597616868⟩]
theorem checked21954 : checkPrefixCuts (2^48) 2881486849 9 Manual.Count131072.C021954.packed 128 cuts21954 = true := by
 decide +kernel
def pointBounds21954 : List (Nat × Nat × Nat) := [(2881570816,101226671229869,101227052298895)]
theorem point_links_checked21954 : (cuts21954.take 1).map (fun c => (2881486849-1+2*2^9*c.k,101226289389033+c.lower,101226670457844+c.upper)) = pointBounds21954 := by
 decide +kernel
def cuts21955 : List PrefixCut := [⟨42,193208537,193208646⟩,
⟨128,583523834,583524171⟩]
theorem checked21955 : checkPrefixCuts (2^48) 2881617921 9 Manual.Count131072.C021955.packed 128 cuts21955 = true := by
 decide +kernel
def pointBounds21955 : List (Nat × Nat × Nat) := [(2881660928,101227080214101,101227461283358)]
theorem point_links_checked21955 : (cuts21955.take 1).map (fun c => (2881617921-1+2*2^9*c.k,101226887005564+c.lower,101227268074712+c.upper)) = pointBounds21955 := by
 decide +kernel
def cuts21956 : List PrefixCut := [⟨2,9669823,9669829⟩,
⟨90,416772652,416772888⟩,
⟨128,589650741,589651075⟩]
theorem checked21956 : checkPrefixCuts (2^48) 2881748993 9 Manual.Count131072.C021956.packed 128 cuts21956 = true := by
 decide +kernel
def pointBounds21956 : List (Nat × Nat × Nat) := [(2881751040,101227480199221,101227861268712),(2881841152,101227887302050,101228268371771)]
theorem point_links_checked21956 : (cuts21956.take 2).map (fun c => (2881748993-1+2*2^9*c.k,101227470529398+c.lower,101227851598883+c.upper)) = pointBounds21956 := by
 decide +kernel
def cuts21957 : List PrefixCut := [⟨50,223370667,223370798⟩,
⟨128,576536328,576536665⟩]
theorem checked21957 : checkPrefixCuts (2^48) 2881880065 9 Manual.Count131072.C021957.packed 128 cuts21957 = true := by
 decide +kernel
def pointBounds21957 : List (Nat × Nat × Nat) := [(2881931264,101228283550806,101228664620756)]
theorem point_links_checked21957 : (cuts21957.take 1).map (fun c => (2881880065-1+2*2^9*c.k,101228060180139+c.lower,101228441249958+c.upper)) = pointBounds21957 := by
 decide +kernel
def cuts21958 : List PrefixCut := [⟨10,43656685,43656709⟩,
⟨98,443298863,443299119⟩,
⟨128,580025950,580026287⟩]
theorem checked21958 : checkPrefixCuts (2^48) 2882011137 9 Manual.Count131072.C021958.packed 128 cuts21958 = true := by
 decide +kernel
def pointBounds21958 : List (Nat × Nat × Nat) := [(2882021376,101228680373152,101229061443332),(2882111488,101229080015330,101229461085742)]
theorem point_links_checked21958 : (cuts21958.take 2).map (fun c => (2882011137-1+2*2^9*c.k,101228636716467+c.lower,101229017786623+c.upper)) = pointBounds21958 := by
 decide +kernel
def cuts21959 : List PrefixCut := [⟨58,267297309,267297467⟩,
⟨128,590449201,590449539⟩]
theorem checked21959 : checkPrefixCuts (2^48) 2882142209 9 Manual.Count131072.C021959.packed 128 cuts21959 = true := by
 decide +kernel
def pointBounds21959 : List (Nat × Nat × Nat) := [(2882201600,101229484039726,101229865110377)]
theorem point_links_checked21959 : (cuts21959.take 1).map (fun c => (2882142209-1+2*2^9*c.k,101229216742417+c.lower,101229597812910+c.upper)) = pointBounds21959 := by
 decide +kernel
def cuts21960 : List PrefixCut := [⟨18,83399026,83399075⟩,
⟨106,490718463,490718744⟩,
⟨128,591789519,591789857⟩]
theorem checked21960 : checkPrefixCuts (2^48) 2882273281 9 Manual.Count131072.C021960.packed 128 cuts21960 = true := by
 decide +kernel
def pointBounds21960 : List (Nat × Nat × Nat) := [(2882291712,101229890590644,101230271661524),(2882381824,101230297910081,101230678981193)]
theorem point_links_checked21960 : (cuts21960.take 2).map (fun c => (2882273281-1+2*2^9*c.k,101229807191618+c.lower,101230188262449+c.upper)) = pointBounds21960 := by
 decide +kernel
def cuts21961 : List PrefixCut := [⟨66,299595321,299595488⟩,
⟨128,581313996,581314325⟩]
theorem checked21961 : checkPrefixCuts (2^48) 2882404353 9 Manual.Count131072.C021961.packed 128 cuts21961 = true := by
 decide +kernel
def pointBounds21961 : List (Nat × Nat × Nat) := [(2882471936,101230698576458,101231079647794)]
theorem point_links_checked21961 : (cuts21961.take 1).map (fun c => (2882404353-1+2*2^9*c.k,101230398981137+c.lower,101230780052306+c.upper)) = pointBounds21961 := by
 decide +kernel
def cuts21962 : List PrefixCut := [⟨26,115908083,115908150⟩,
⟨114,511764731,511765029⟩,
⟨128,573475852,573476184⟩]
theorem checked21962 : checkPrefixCuts (2^48) 2882535425 9 Manual.Count131072.C021962.packed 128 cuts21962 = true := by
 decide +kernel
def pointBounds21962 : List (Nat × Nat × Nat) := [(2882562048,101231096203216,101231477274781),(2882652160,101231492059864,101231873131660)]
theorem point_links_checked21962 : (cuts21962.take 2).map (fun c => (2882535425-1+2*2^9*c.k,101230980295133+c.lower,101231361366631+c.upper)) = pointBounds21962 := by
 decide +kernel
def cuts21963 : List PrefixCut := [⟨74,353856958,353857158⟩,
⟨128,601375457,601375799⟩]
theorem checked21963 : checkPrefixCuts (2^48) 2882666497 9 Manual.Count131072.C021963.packed 128 cuts21963 = true := by
 decide +kernel
def pointBounds21963 : List (Nat × Nat × Nat) := [(2882742272,101231907627943,101232288699973)]
theorem point_links_checked21963 : (cuts21963.take 1).map (fun c => (2882666497-1+2*2^9*c.k,101231553770985+c.lower,101231934842815+c.upper)) = pointBounds21963 := by
 decide +kernel
def cuts21964 : List PrefixCut := [⟨34,149778078,149778163⟩,
⟨122,554189689,554190007⟩,
⟨128,580258276,580258610⟩]
theorem checked21964 : checkPrefixCuts (2^48) 2882797569 9 Manual.Count131072.C021964.packed 128 cuts21964 = true := by
 decide +kernel
def pointBounds21964 : List (Nat × Nat × Nat) := [(2882832384,101232304924520,101232685996777),(2882922496,101232709336131,101233090408621)]
theorem point_links_checked21964 : (cuts21964.take 2).map (fun c => (2882797569-1+2*2^9*c.k,101232155146442+c.lower,101232536218614+c.upper)) = pointBounds21964 := by
 decide +kernel
def cuts21965 : List PrefixCut := [⟨82,380380602,380380826⟩,
⟨128,592143120,592143470⟩]
theorem checked21965 : checkPrefixCuts (2^48) 2882928641 9 Manual.Count131072.C021965.packed 128 cuts21965 = true := by
 decide +kernel
def pointBounds21965 : List (Nat × Nat × Nat) := [(2883012608,101233115785320,101233496858050)]
theorem point_links_checked21965 : (cuts21965.take 1).map (fun c => (2882928641-1+2*2^9*c.k,101232735404718+c.lower,101233116477224+c.upper)) = pointBounds21965 := by
 decide +kernel
def cuts21966 : List PrefixCut := [⟨42,198383913,198384027⟩,
⟨128,588894555,588894889⟩]
theorem checked21966 : checkPrefixCuts (2^48) 2883059713 9 Manual.Count131072.C021966.packed 128 cuts21966 = true := by
 decide +kernel
def pointBounds21966 : List (Nat × Nat × Nat) := [(2883102720,101233525931751,101233907004721)]
theorem point_links_checked21966 : (cuts21966.take 1).map (fun c => (2883059713-1+2*2^9*c.k,101233327547838+c.lower,101233708620694+c.upper)) = pointBounds21966 := by
 decide +kernel
def cuts21967 : List PrefixCut := [⟨2,10641249,10641255⟩,
⟨90,413049710,413049955⟩,
⟨128,584767498,584767838⟩]
theorem checked21967 : checkPrefixCuts (2^48) 2883190785 9 Manual.Count131072.C021967.packed 128 cuts21967 = true := by
 decide +kernel
def pointBounds21967 : List (Nat × Nat × Nat) := [(2883192832,101233927083642,101234308156838),(2883282944,101234329492103,101234710565538)]
theorem point_links_checked21967 : (cuts21967.take 2).map (fun c => (2883190785-1+2*2^9*c.k,101233916442393+c.lower,101234297515583+c.upper)) = pointBounds21967 := by
 decide +kernel
def cuts21968 : List PrefixCut := [⟨50,235168699,235168829⟩,
⟨128,601238649,601238987⟩]
theorem checked21968 : checkPrefixCuts (2^48) 2883321857 9 Manual.Count131072.C021968.packed 128 cuts21968 = true := by
 decide +kernel
def pointBounds21968 : List (Nat × Nat × Nat) := [(2883373056,101234736378590,101235117452250)]
theorem point_links_checked21968 : (cuts21968.take 1).map (fun c => (2883321857-1+2*2^9*c.k,101234501209891+c.lower,101234882283421+c.upper)) = pointBounds21968 := by
 decide +kernel
def cuts21969 : List PrefixCut := [⟨10,47344307,47344331⟩,
⟨98,453522100,453522362⟩,
⟨128,591352221,591352559⟩]
theorem checked21969 : checkPrefixCuts (2^48) 2883452929 9 Manual.Count131072.C021969.packed 128 cuts21969 = true := by
 decide +kernel
def pointBounds21969 : List (Nat × Nat × Nat) := [(2883463168,101235149792847,101235530866739),(2883553280,101235555970640,101235937044770)]
theorem point_links_checked21969 : (cuts21969.take 2).map (fun c => (2883452929-1+2*2^9*c.k,101235102448540+c.lower,101235483522408+c.upper)) = pointBounds21969 := by
 decide +kernel
def cuts21970 : List PrefixCut := [⟨58,267066084,267066238⟩,
⟨128,581369137,581369477⟩]
theorem checked21970 : checkPrefixCuts (2^48) 2883584001 9 Manual.Count131072.C021970.packed 128 cuts21970 = true := by
 decide +kernel
def pointBounds21970 : List (Nat × Nat × Nat) := [(2883643392,101235960866845,101236341941205)]
theorem point_links_checked21970 : (cuts21970.take 1).map (fun c => (2883584001-1+2*2^9*c.k,101235693800761+c.lower,101236074874967+c.upper)) = pointBounds21970 := by
 decide +kernel
def cuts21971 : List PrefixCut := [⟨19,84919045,84919097⟩,
⟨108,491351390,491351675⟩,
⟨128,584368325,584368660⟩]
theorem checked21971 : checkPrefixCuts (2^48) 2883715073 9 Manual.Count131072.C021971.packed 128 cuts21971 = true := by
 decide +kernel
def pointBounds21971 : List (Nat × Nat × Nat) := [(2883734528,101236360088943,101236741163541),(2883825664,101236766521288,101237147596119)]
theorem point_links_checked21971 : (cuts21971.take 2).map (fun c => (2883715073-1+2*2^9*c.k,101236275169898+c.lower,101236656244444+c.upper)) = pointBounds21971 := by
 decide +kernel
def cuts21972 : List PrefixCut := [⟨69,317209094,317209268⟩,
⟨128,583463448,583463776⟩]
theorem checked21972 : checkPrefixCuts (2^48) 2883846145 9 Manual.Count131072.C021972.packed 128 cuts21972 = true := by
 decide +kernel
def pointBounds21972 : List (Nat × Nat × Nat) := [(2883916800,101237176747317,101237557822372)]
theorem point_links_checked21972 : (cuts21972.take 1).map (fun c => (2883846145-1+2*2^9*c.k,101236859538223+c.lower,101237240613104+c.upper)) = pointBounds21972 := by
 decide +kernel
def cuts21973 : List PrefixCut := [⟨30,136541055,136541130⟩,
⟨119,543130050,543130360⟩,
⟨128,583924877,583925209⟩]
theorem checked21973 : checkPrefixCuts (2^48) 2883977217 9 Manual.Count131072.C021973.packed 128 cuts21973 = true := by
 decide +kernel
def pointBounds21973 : List (Nat × Nat × Nat) := [(2884007936,101237579542726,101237960618010),(2884099072,101237986131721,101238367207240)]
theorem point_links_checked21973 : (cuts21973.take 2).map (fun c => (2883977217-1+2*2^9*c.k,101237443001671+c.lower,101237824076880+c.upper)) = pointBounds21973 := by
 decide +kernel
def cuts21974 : List PrefixCut := [⟨80,372905618,372905837⟩,
⟨128,591608212,591608556⟩]
theorem checked21974 : checkPrefixCuts (2^48) 2884108289 9 Manual.Count131072.C021974.packed 128 cuts21974 = true := by
 decide +kernel
def pointBounds21974 : List (Nat × Nat × Nat) := [(2884190208,101238399832166,101238780907926)]
theorem point_links_checked21974 : (cuts21974.take 1).map (fun c => (2884108289-1+2*2^9*c.k,101238026926548+c.lower,101238408002089+c.upper)) = pointBounds21974 := by
 decide +kernel
def cuts21975 : List PrefixCut := [⟨41,188153474,188153589⟩,
⟨128,582895955,582896301⟩]
theorem checked21975 : checkPrefixCuts (2^48) 2884239361 9 Manual.Count131072.C021975.packed 128 cuts21975 = true := by
 decide +kernel
def pointBounds21975 : List (Nat × Nat × Nat) := [(2884281344,101238806688234,101239187764234)]
theorem point_links_checked21975 : (cuts21975.take 1).map (fun c => (2884239361-1+2*2^9*c.k,101238618534760+c.lower,101238999610645+c.upper)) = pointBounds21975 := by
 decide +kernel
def cuts21976 : List PrefixCut := [⟨2,8392414,8392420⟩,
⟨91,419906864,419907103⟩,
⟨128,590188242,590188582⟩]
theorem checked21976 : checkPrefixCuts (2^48) 2884370433 9 Manual.Count131072.C021976.packed 128 cuts21976 = true := by
 decide +kernel
def pointBounds21976 : List (Nat × Nat × Nat) := [(2884372480,101239209823129,101239590899366),(2884463616,101239621337579,101240002414049)]
theorem point_links_checked21976 : (cuts21976.take 2).map (fun c => (2884370433-1+2*2^9*c.k,101239201430715+c.lower,101239582506946+c.upper)) = pointBounds21976 := by
 decide +kernel
def cuts21977 : List PrefixCut := [⟨52,239658742,239658872⟩,
⟨128,592600950,592601283⟩]
theorem checked21977 : checkPrefixCuts (2^48) 2884501505 9 Manual.Count131072.C021977.packed 128 cuts21977 = true := by
 decide +kernel
def pointBounds21977 : List (Nat × Nat × Nat) := [(2884554752,101240031277699,101240412354400)]
theorem point_links_checked21977 : (cuts21977.take 1).map (fun c => (2884501505-1+2*2^9*c.k,101239791618957+c.lower,101240172695528+c.upper)) = pointBounds21977 := by
 decide +kernel
def cuts21978 : List PrefixCut := [⟨13,58448721,58448755⟩,
⟨102,466313891,466314155⟩,
⟨128,587207332,587207663⟩]
theorem checked21978 : checkPrefixCuts (2^48) 2884632577 9 Manual.Count131072.C021978.packed 128 cuts21978 = true := by
 decide +kernel
def pointBounds21978 : List (Nat × Nat × Nat) := [(2884645888,101240442668628,101240823745566),(2884737024,101240850533798,101241231610966)]
theorem point_links_checked21978 : (cuts21978.take 2).map (fun c => (2884632577-1+2*2^9*c.k,101240384219907+c.lower,101240765296811+c.upper)) = pointBounds21978 := by
 decide +kernel
def cuts21979 : List PrefixCut := [⟨63,285592862,285593026⟩,
⟨128,581911923,581912254⟩]
theorem checked21979 : checkPrefixCuts (2^48) 2884763649 9 Manual.Count131072.C021979.packed 128 cuts21979 = true := by
 decide +kernel
def pointBounds21979 : List (Nat × Nat × Nat) := [(2884828160,101241257020101,101241638097500)]
theorem point_links_checked21979 : (cuts21979.take 1).map (fun c => (2884763649-1+2*2^9*c.k,101240971427239+c.lower,101241352504474+c.upper)) = pointBounds21979 := by
 decide +kernel
def cuts21980 : List PrefixCut := [⟨24,106934641,106934705⟩,
⟨113,517005144,517005443⟩,
⟨128,581885433,581885768⟩]
theorem checked21980 : checkPrefixCuts (2^48) 2884894721 9 Manual.Count131072.C021980.packed 128 cuts21980 = true := by
 decide +kernel
def pointBounds21980 : List (Nat × Nat × Nat) := [(2884919296,101241660273803,101242041351433),(2885010432,101242070344306,101242451422171)]
theorem point_links_checked21980 : (cuts21980.take 2).map (fun c => (2884894721-1+2*2^9*c.k,101241553339162+c.lower,101241934416728+c.upper)) = pointBounds21980 := by
 decide +kernel
def cuts21981 : List PrefixCut := [⟨74,338445364,338445559⟩,
⟨128,581761454,581761790⟩]
theorem checked21981 : checkPrefixCuts (2^48) 2885025793 9 Manual.Count131072.C021981.packed 128 cuts21981 = true := by
 decide +kernel
def pointBounds21981 : List (Nat × Nat × Nat) := [(2885101568,101242473669959,101242854748055)]
theorem point_links_checked21981 : (cuts21981.take 1).map (fun c => (2885025793-1+2*2^9*c.k,101242135224595+c.lower,101242516302496+c.upper)) = pointBounds21981 := by
 decide +kernel
def cuts21982 : List PrefixCut := [⟨35,162338255,162338349⟩,
⟨124,575882002,575882328⟩,
⟨128,591588402,591588740⟩]
theorem checked21982 : checkPrefixCuts (2^48) 2885156865 9 Manual.Count131072.C021982.packed 128 cuts21982 = true := by
 decide +kernel
def pointBounds21982 : List (Nat × Nat × Nat) := [(2885192704,101242879324304,101243260402635),(2885283840,101243292868051,101243673946614)]
theorem point_links_checked21982 : (cuts21982.take 2).map (fun c => (2885156865-1+2*2^9*c.k,101242716986049+c.lower,101243098064286+c.upper)) = pointBounds21982 := by
 decide +kernel
def cuts21983 : List PrefixCut := [⟨85,388849227,388849452⟩,
⟨128,584342515,584342851⟩]
theorem checked21983 : checkPrefixCuts (2^48) 2885287937 9 Manual.Count131072.C021983.packed 128 cuts21983 = true := by
 decide +kernel
def pointBounds21983 : List (Nat × Nat × Nat) := [(2885374976,101243697423678,101244078502478)]
theorem point_links_checked21983 : (cuts21983.take 1).map (fun c => (2885287937-1+2*2^9*c.k,101243308574451+c.lower,101243689653026+c.upper)) = pointBounds21983 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000061
