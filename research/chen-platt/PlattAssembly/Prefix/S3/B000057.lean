import PlattAssemblyKernel
import PlattCertificates.Count131072.C021824
import PlattCertificates.Count131072.C021825
import PlattCertificates.Count131072.C021826
import PlattCertificates.Count131072.C021827
import PlattCertificates.Count131072.C021828
import PlattCertificates.Count131072.C021829
import PlattCertificates.Count131072.C021830
import PlattCertificates.Count131072.C021831
import PlattCertificates.Count131072.C021832
import PlattCertificates.Count131072.C021833
import PlattCertificates.Count131072.C021834
import PlattCertificates.Count131072.C021835
import PlattCertificates.Count131072.C021836
import PlattCertificates.Count131072.C021837
import PlattCertificates.Count131072.C021838
import PlattCertificates.Count131072.C021839
import PlattCertificates.Count131072.C021840
import PlattCertificates.Count131072.C021841
import PlattCertificates.Count131072.C021842
import PlattCertificates.Count131072.C021843
import PlattCertificates.Count131072.C021844
import PlattCertificates.Count131072.C021845
import PlattCertificates.Count131072.C021846
import PlattCertificates.Count131072.C021847
import PlattCertificates.Count131072.C021848
import PlattCertificates.Count131072.C021849
import PlattCertificates.Count131072.C021850
import PlattCertificates.Count131072.C021851
import PlattCertificates.Count131072.C021852
import PlattCertificates.Count131072.C021853
import PlattCertificates.Count131072.C021854
import PlattCertificates.Count131072.C021855
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000057
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts21824 : List PrefixCut := [⟨2,10416085,10416091⟩,
⟨90,414769836,414770071⟩,
⟨128,593899927,593900265⟩]
theorem checked21824 : checkPrefixCuts (2^48) 2864447489 9 Manual.Count131072.C021824.packed 128 cuts21824 = true := by
 decide +kernel
def pointBounds21824 : List (Nat × Nat × Nat) := [(2864449536,101149634161655,101150015186637),(2864539648,101150038515406,101150419540617)]
theorem point_links_checked21824 : (cuts21824.take 2).map (fun c => (2864447489-1+2*2^9*c.k,101149623745570+c.lower,101150004770546+c.upper)) = pointBounds21824 := by
 decide +kernel
def cuts21825 : List PrefixCut := [⟨50,229436206,229436335⟩,
⟨128,585324323,585324662⟩]
theorem checked21825 : checkPrefixCuts (2^48) 2864578561 9 Manual.Count131072.C021825.packed 128 cuts21825 = true := by
 decide +kernel
def pointBounds21825 : List (Nat × Nat × Nat) := [(2864629760,101150447081703,101150828107146)]
theorem point_links_checked21825 : (cuts21825.take 1).map (fun c => (2864578561-1+2*2^9*c.k,101150217645497+c.lower,101150598670811+c.upper)) = pointBounds21825 := by
 decide +kernel
def cuts21826 : List PrefixCut := [⟨10,45099420,45099448⟩,
⟨98,458159616,458159883⟩,
⟨128,597874017,597874364⟩]
theorem checked21826 : checkPrefixCuts (2^48) 2864709633 9 Manual.Count131072.C021826.packed 128 cuts21826 = true := by
 decide +kernel
def pointBounds21826 : List (Nat × Nat × Nat) := [(2864719872,101150848069240,101151229094921),(2864809984,101151261129436,101151642155356)]
theorem point_links_checked21826 : (cuts21826.take 2).map (fun c => (2864709633-1+2*2^9*c.k,101150802969820+c.lower,101151183995473+c.upper)) = pointBounds21826 := by
 decide +kernel
def cuts21827 : List PrefixCut := [⟨58,271171324,271171474⟩,
⟨128,594702658,594702997⟩]
theorem checked21827 : checkPrefixCuts (2^48) 2864840705 9 Manual.Count131072.C021827.packed 128 cuts21827 = true := by
 decide +kernel
def pointBounds21827 : List (Nat × Nat × Nat) := [(2864900096,101151672015161,101152053041311)]
theorem point_links_checked21827 : (cuts21827.take 1).map (fun c => (2864840705-1+2*2^9*c.k,101151400843837+c.lower,101151781869837+c.upper)) = pointBounds21827 := by
 decide +kernel
def cuts21828 : List PrefixCut := [⟨18,82330727,82330773⟩,
⟨106,481990711,481990989⟩,
⟨128,584851030,584851368⟩]
theorem checked21828 : checkPrefixCuts (2^48) 2864971777 9 Manual.Count131072.C021828.packed 128 cuts21828 = true := by
 decide +kernel
def pointBounds21828 : List (Nat × Nat × Nat) := [(2864990208,101152077877222,101152458903607),(2865080320,101152477537206,101152858563823)]
theorem point_links_checked21828 : (cuts21828.take 2).map (fun c => (2864971777-1+2*2^9*c.k,101151995546495+c.lower,101152376572834+c.upper)) = pointBounds21828 := by
 decide +kernel
def cuts21829 : List PrefixCut := [⟨66,306316541,306316713⟩,
⟨128,589736365,589736696⟩]
theorem checked21829 : checkPrefixCuts (2^48) 2865102849 9 Manual.Count131072.C021829.packed 128 cuts21829 = true := by
 decide +kernel
def pointBounds21829 : List (Nat × Nat × Nat) := [(2865170432,101152886714066,101153267740915)]
theorem point_links_checked21829 : (cuts21829.take 1).map (fun c => (2865102849-1+2*2^9*c.k,101152580397525+c.lower,101152961424202+c.upper)) = pointBounds21829 := by
 decide +kernel
def cuts21830 : List PrefixCut := [⟨26,122796956,122797023⟩,
⟨114,531653394,531653692⟩,
⟨128,597273554,597273887⟩]
theorem checked21830 : checkPrefixCuts (2^48) 2865233921 9 Manual.Count131072.C021830.packed 128 cuts21830 = true := by
 decide +kernel
def pointBounds21830 : List (Nat × Nat × Nat) := [(2865260544,101153292930846,101153673957921),(2865350656,101153701787284,101154082814590)]
theorem point_links_checked21830 : (cuts21830.take 2).map (fun c => (2865233921-1+2*2^9*c.k,101153170133890+c.lower,101153551160898+c.upper)) = pointBounds21830 := by
 decide +kernel
def cuts21831 : List PrefixCut := [⟨74,341946367,341946560⟩,
⟨128,592923941,592924279⟩]
theorem checked21831 : checkPrefixCuts (2^48) 2865364993 9 Manual.Count131072.C021831.packed 128 cuts21831 = true := by
 decide +kernel
def pointBounds21831 : List (Nat × Nat × Nat) := [(2865440768,101154109353811,101154490381345)]
theorem point_links_checked21831 : (cuts21831.take 1).map (fun c => (2865364993-1+2*2^9*c.k,101153767407444+c.lower,101154148434785+c.upper)) = pointBounds21831 := by
 decide +kernel
def cuts21832 : List PrefixCut := [⟨34,157165485,157165577⟩,
⟨122,564608120,564608444⟩,
⟨128,591226998,591227337⟩]
theorem checked21832 : checkPrefixCuts (2^48) 2865496065 9 Manual.Count131072.C021832.packed 128 cuts21832 = true := by
 decide +kernel
def pointBounds21832 : List (Nat × Nat × Nat) := [(2865530880,101154517496870,101154898524641),(2865620992,101154924939505,101155305967508)]
theorem point_links_checked21832 : (cuts21832.take 2).map (fun c => (2865496065-1+2*2^9*c.k,101154360331385+c.lower,101154741359064+c.upper)) = pointBounds21832 := by
 decide +kernel
def cuts21833 : List PrefixCut := [⟨82,382382521,382382738⟩,
⟨128,594834218,594834549⟩]
theorem checked21833 : checkPrefixCuts (2^48) 2865627137 9 Manual.Count131072.C021833.packed 128 cuts21833 = true := by
 decide +kernel
def pointBounds21833 : List (Nat × Nat × Nat) := [(2865711104,101155333940904,101155714969139)]
theorem point_links_checked21833 : (cuts21833.take 1).map (fun c => (2865627137-1+2*2^9*c.k,101154951558383+c.lower,101155332586401+c.upper)) = pointBounds21833 := by
 decide +kernel
def cuts21834 : List PrefixCut := [⟨42,194965334,194965444⟩,
⟨128,592056908,592057245⟩]
theorem checked21834 : checkPrefixCuts (2^48) 2865758209 9 Manual.Count131072.C021834.packed 128 cuts21834 = true := by
 decide +kernel
def pointBounds21834 : List (Nat × Nat × Nat) := [(2865801216,101155741357935,101156122386394)]
theorem point_links_checked21834 : (cuts21834.take 1).map (fun c => (2865758209-1+2*2^9*c.k,101155546392601+c.lower,101155927420950+c.upper)) = pointBounds21834 := by
 decide +kernel
def cuts21835 : List PrefixCut := [⟨2,9821552,9821557⟩,
⟨90,424186094,424186331⟩,
⟨128,598217270,598217606⟩]
theorem checked21835 : checkPrefixCuts (2^48) 2865889281 9 Manual.Count131072.C021835.packed 128 cuts21835 = true := by
 decide +kernel
def pointBounds21835 : List (Nat × Nat × Nat) := [(2865891328,101156148271061,101156529299752),(2865981440,101156562635603,101156943664526)]
theorem point_links_checked21835 : (cuts21835.take 2).map (fun c => (2865889281-1+2*2^9*c.k,101156138449509+c.lower,101156519478195+c.upper)) = pointBounds21835 := by
 decide +kernel
def cuts21836 : List PrefixCut := [⟨50,232463506,232463639⟩,
⟨128,587779727,587780068⟩]
theorem checked21836 : checkPrefixCuts (2^48) 2866020353 9 Manual.Count131072.C021836.packed 128 cuts21836 = true := by
 decide +kernel
def pointBounds21836 : List (Nat × Nat × Nat) := [(2866071552,101156969130285,101157350159440)]
theorem point_links_checked21836 : (cuts21836.take 1).map (fun c => (2866020353-1+2*2^9*c.k,101156736666779+c.lower,101157117695801+c.upper)) = pointBounds21836 := by
 decide +kernel
def cuts21837 : List PrefixCut := [⟨10,45862388,45862412⟩,
⟨98,455081202,455081461⟩,
⟨128,592663050,592663391⟩]
theorem checked21837 : checkPrefixCuts (2^48) 2866151425 9 Manual.Count131072.C021837.packed 128 cuts21837 = true := by
 decide +kernel
def pointBounds21837 : List (Nat × Nat × Nat) := [(2866161664,101157370308894,101157751338281),(2866251776,101157779527708,101158160557330)]
theorem point_links_checked21837 : (cuts21837.take 2).map (fun c => (2866151425-1+2*2^9*c.k,101157324446506+c.lower,101157705475869+c.upper)) = pointBounds21837 := by
 decide +kernel
def cuts21838 : List PrefixCut := [⟨58,267597874,267598029⟩,
⟨128,584681888,584682226⟩]
theorem checked21838 : checkPrefixCuts (2^48) 2866282497 9 Manual.Count131072.C021838.packed 128 cuts21838 = true := by
 decide +kernel
def pointBounds21838 : List (Nat × Nat × Nat) := [(2866341888,101158184707430,101158565737289)]
theorem point_links_checked21838 : (cuts21838.take 1).map (fun c => (2866282497-1+2*2^9*c.k,101157917109556+c.lower,101158298139260+c.upper)) = pointBounds21838 := by
 decide +kernel
def cuts21839 : List PrefixCut := [⟨18,84940643,84940693⟩,
⟨106,489309342,489309626⟩,
⟨128,591921526,591921871⟩]
theorem checked21839 : checkPrefixCuts (2^48) 2866413569 9 Manual.Count131072.C021839.packed 128 cuts21839 = true := by
 decide +kernel
def pointBounds21839 : List (Nat × Nat × Nat) := [(2866432000,101158586732087,101158967762179),(2866522112,101158991100786,101159372131112)]
theorem point_links_checked21839 : (cuts21839.take 2).map (fun c => (2866413569-1+2*2^9*c.k,101158501791444+c.lower,101158882821486+c.upper)) = pointBounds21839 := by
 decide +kernel
def cuts21840 : List PrefixCut := [⟨66,306358876,306359054⟩,
⟨128,593563703,593564046⟩]
theorem checked21840 : checkPrefixCuts (2^48) 2866544641 9 Manual.Count131072.C021840.packed 128 cuts21840 = true := by
 decide +kernel
def pointBounds21840 : List (Nat × Nat × Nat) := [(2866612224,101159400071846,101159781102411)]
theorem point_links_checked21840 : (cuts21840.take 1).map (fun c => (2866544641-1+2*2^9*c.k,101159093712970+c.lower,101159474743357+c.upper)) = pointBounds21840 := by
 decide +kernel
def cuts21841 : List PrefixCut := [⟨26,115960217,115960285⟩,
⟨114,522450877,522451172⟩,
⟨128,583128817,583129147⟩]
theorem checked21841 : checkPrefixCuts (2^48) 2866675713 9 Manual.Count131072.C021841.packed 128 cuts21841 = true := by
 decide +kernel
def pointBounds21841 : List (Nat × Nat × Nat) := [(2866702336,101159803236890,101160184267688),(2866792448,101160209727550,101160590758575)]
theorem point_links_checked21841 : (cuts21841.take 2).map (fun c => (2866675713-1+2*2^9*c.k,101159687276673+c.lower,101160068307403+c.upper)) = pointBounds21841 := by
 decide +kernel
def cuts21842 : List PrefixCut := [⟨74,338043452,338043642⟩,
⟨128,587618479,587618813⟩]
theorem checked21842 : checkPrefixCuts (2^48) 2866806785 9 Manual.Count131072.C021842.packed 128 cuts21842 = true := by
 decide +kernel
def pointBounds21842 : List (Nat × Nat × Nat) := [(2866882560,101160608448942,101160989480192)]
theorem point_links_checked21842 : (cuts21842.take 1).map (fun c => (2866806785-1+2*2^9*c.k,101160270405490+c.lower,101160651436550+c.upper)) = pointBounds21842 := by
 decide +kernel
def cuts21843 : List PrefixCut := [⟨34,159344574,159344663⟩,
⟨122,564422480,564422794⟩,
⟨128,591617025,591617354⟩]
theorem checked21843 : checkPrefixCuts (2^48) 2866937857 9 Manual.Count131072.C021843.packed 128 cuts21843 = true := by
 decide +kernel
def pointBounds21843 : List (Nat × Nat × Nat) := [(2866972672,101161017368543,101161398400026),(2867062784,101161422446449,101161803478157)]
theorem point_links_checked21843 : (cuts21843.take 2).map (fun c => (2866937857-1+2*2^9*c.k,101160858023969+c.lower,101161239055363+c.upper)) = pointBounds21843 := by
 decide +kernel
def cuts21844 : List PrefixCut := [⟨82,373550952,373551171⟩,
⟨128,586288513,586288854⟩]
theorem checked21844 : checkPrefixCuts (2^48) 2867068929 9 Manual.Count131072.C021844.packed 128 cuts21844 = true := by
 decide +kernel
def pointBounds21844 : List (Nat × Nat × Nat) := [(2867152896,101161823191946,101162204223888)]
theorem point_links_checked21844 : (cuts21844.take 1).map (fun c => (2867068929-1+2*2^9*c.k,101161449640994+c.lower,101161830672717+c.upper)) = pointBounds21844 := by
 decide +kernel
def cuts21845 : List PrefixCut := [⟨42,200855628,200855741⟩,
⟨128,589305066,589305398⟩]
theorem checked21845 : checkPrefixCuts (2^48) 2867200001 9 Manual.Count131072.C021845.packed 128 cuts21845 = true := by
 decide +kernel
def pointBounds21845 : List (Nat × Nat × Nat) := [(2867243008,101162236785135,101162617817312)]
theorem point_links_checked21845 : (cuts21845.take 1).map (fun c => (2867200001-1+2*2^9*c.k,101162035929507+c.lower,101162416961571+c.upper)) = pointBounds21845 := by
 decide +kernel
def cuts21846 : List PrefixCut := [⟨2,9620281,9620286⟩,
⟨90,413272950,413273187⟩,
⟨128,589376222,589376562⟩]
theorem checked21846 : checkPrefixCuts (2^48) 2867331073 9 Manual.Count131072.C021846.packed 128 cuts21846 = true := by
 decide +kernel
def pointBounds21846 : List (Nat × Nat × Nat) := [(2867333120,101162634854854,101163015887255),(2867423232,101163038507523,101163419540156)]
theorem point_links_checked21846 : (cuts21846.take 2).map (fun c => (2867331073-1+2*2^9*c.k,101162625234573+c.lower,101163006266969+c.upper)) = pointBounds21846 := by
 decide +kernel
def cuts21847 : List PrefixCut := [⟨50,229009139,229009276⟩,
⟨128,590330798,590331136⟩]
theorem checked21847 : checkPrefixCuts (2^48) 2867462145 9 Manual.Count131072.C021847.packed 128 cuts21847 = true := by
 decide +kernel
def pointBounds21847 : List (Nat × Nat × Nat) := [(2867513344,101163443619934,101163824652807)]
theorem point_links_checked21847 : (cuts21847.take 1).map (fun c => (2867462145-1+2*2^9*c.k,101163214610795+c.lower,101163595643531+c.upper)) = pointBounds21847 := by
 decide +kernel
def cuts21848 : List PrefixCut := [⟨10,46722740,46722765⟩,
⟨98,451613328,451613587⟩,
⟨128,594131812,594132151⟩]
theorem checked21848 : checkPrefixCuts (2^48) 2867593217 9 Manual.Count131072.C021848.packed 128 cuts21848 = true := by
 decide +kernel
def pointBounds21848 : List (Nat × Nat × Nat) := [(2867603456,101163851664333,101164232697432),(2867693568,101164256554921,101164637588254)]
theorem point_links_checked21848 : (cuts21848.take 2).map (fun c => (2867593217-1+2*2^9*c.k,101163804941593+c.lower,101164185974667+c.upper)) = pointBounds21848 := by
 decide +kernel
def cuts21849 : List PrefixCut := [⟨58,271487547,271487707⟩,
⟨128,593417789,593418138⟩]
theorem checked21849 : checkPrefixCuts (2^48) 2867724289 9 Manual.Count131072.C021849.packed 128 cuts21849 = true := by
 decide +kernel
def pointBounds21849 : List (Nat × Nat × Nat) := [(2867783680,101164670560952,101165051594525)]
theorem point_links_checked21849 : (cuts21849.take 1).map (fun c => (2867724289-1+2*2^9*c.k,101164399073405+c.lower,101164780106818+c.upper)) = pointBounds21849 := by
 decide +kernel
def cuts21850 : List PrefixCut := [⟨18,83720166,83720215⟩,
⟨106,496522473,496522753⟩,
⟨128,598886788,598887128⟩]
theorem checked21850 : checkPrefixCuts (2^48) 2867855361 9 Manual.Count131072.C021850.packed 128 cuts21850 = true := by
 decide +kernel
def pointBounds21850 : List (Nat × Nat × Nat) := [(2867873792,101165076211360,101165457245171),(2867963904,101165489013667,101165870047709)]
theorem point_links_checked21850 : (cuts21850.take 2).map (fun c => (2867855361-1+2*2^9*c.k,101164992491194+c.lower,101165373524956+c.upper)) = pointBounds21850 := by
 decide +kernel
def cuts21851 : List PrefixCut := [⟨66,302966164,302966331⟩,
⟨128,593657852,593658188⟩]
theorem checked21851 : checkPrefixCuts (2^48) 2867986433 9 Manual.Count131072.C021851.packed 128 cuts21851 = true := by
 decide +kernel
def pointBounds21851 : List (Nat × Nat × Nat) := [(2868054016,101165894344146,101166275378415)]
theorem point_links_checked21851 : (cuts21851.take 1).map (fun c => (2867986433-1+2*2^9*c.k,101165591377982+c.lower,101165972412084+c.upper)) = pointBounds21851 := by
 decide +kernel
def cuts21852 : List PrefixCut := [⟨26,121299546,121299619⟩,
⟨114,521599556,521599866⟩,
⟨128,586074258,586074605⟩]
theorem checked21852 : checkPrefixCuts (2^48) 2868117505 9 Manual.Count131072.C021852.packed 128 cuts21852 = true := by
 decide +kernel
def pointBounds21852 : List (Nat × Nat × Nat) := [(2868144128,101166306335380,101166687369891),(2868234240,101166706635390,101167087670138)]
theorem point_links_checked21852 : (cuts21852.take 2).map (fun c => (2868117505-1+2*2^9*c.k,101166185035834+c.lower,101166566070272+c.upper)) = pointBounds21852 := by
 decide +kernel
def cuts21853 : List PrefixCut := [⟨74,339345567,339345760⟩,
⟨128,584673650,584673987⟩]
theorem checked21853 : checkPrefixCuts (2^48) 2868248577 9 Manual.Count131072.C021853.packed 128 cuts21853 = true := by
 decide +kernel
def pointBounds21853 : List (Nat × Nat × Nat) := [(2868324352,101167110455659,101167491490637)]
theorem point_links_checked21853 : (cuts21853.take 1).map (fun c => (2868248577-1+2*2^9*c.k,101166771110092+c.lower,101167152144877+c.upper)) = pointBounds21853 := by
 decide +kernel
def cuts21854 : List PrefixCut := [⟨34,159656982,159657076⟩,
⟨122,568750820,568751147⟩,
⟨128,597011080,597011423⟩]
theorem checked21854 : checkPrefixCuts (2^48) 2868379649 9 Manual.Count131072.C021854.packed 128 cuts21854 = true := by
 decide +kernel
def pointBounds21854 : List (Nat × Nat × Nat) := [(2868414464,101167515440724,101167896475940),(2868504576,101167924534562,101168305570011)]
theorem point_links_checked21854 : (cuts21854.take 2).map (fun c => (2868379649-1+2*2^9*c.k,101167355783742+c.lower,101167736818864+c.upper)) = pointBounds21854 := by
 decide +kernel
def cuts21855 : List PrefixCut := [⟨82,373657531,373657745⟩,
⟨128,587858121,587858454⟩]
theorem checked21855 : checkPrefixCuts (2^48) 2868510721 9 Manual.Count131072.C021855.packed 128 cuts21855 = true := by
 decide +kernel
def pointBounds21855 : List (Nat × Nat × Nat) := [(2868594688,101168326452353,101168707488032)]
theorem point_links_checked21855 : (cuts21855.take 1).map (fun c => (2868510721-1+2*2^9*c.k,101167952794822+c.lower,101168333830287+c.upper)) = pointBounds21855 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000057
