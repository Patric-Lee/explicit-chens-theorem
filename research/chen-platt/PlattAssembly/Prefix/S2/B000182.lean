import PlattAssemblyKernel
import PlattCertificates.Count131072.C015824
import PlattCertificates.Count131072.C015825
import PlattCertificates.Count131072.C015826
import PlattCertificates.Count131072.C015827
import PlattCertificates.Count131072.C015828
import PlattCertificates.Count131072.C015829
import PlattCertificates.Count131072.C015830
import PlattCertificates.Count131072.C015831
import PlattCertificates.Count131072.C015832
import PlattCertificates.Count131072.C015833
import PlattCertificates.Count131072.C015834
import PlattCertificates.Count131072.C015835
import PlattCertificates.Count131072.C015836
import PlattCertificates.Count131072.C015837
import PlattCertificates.Count131072.C015838
import PlattCertificates.Count131072.C015839
import PlattCertificates.Count131072.C015840
import PlattCertificates.Count131072.C015841
import PlattCertificates.Count131072.C015842
import PlattCertificates.Count131072.C015843
import PlattCertificates.Count131072.C015844
import PlattCertificates.Count131072.C015845
import PlattCertificates.Count131072.C015846
import PlattCertificates.Count131072.C015847
import PlattCertificates.Count131072.C015848
import PlattCertificates.Count131072.C015849
import PlattCertificates.Count131072.C015850
import PlattCertificates.Count131072.C015851
import PlattCertificates.Count131072.C015852
import PlattCertificates.Count131072.C015853
import PlattCertificates.Count131072.C015854
import PlattCertificates.Count131072.C015855
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000182
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts15824 : List PrefixCut := [⟨38,251128799,251128961⟩,
⟨102,665602794,665603229⟩,
⟨128,833149514,833150056⟩]
theorem checked15824 : checkPrefixCuts (2^48) 2078015489 9 Manual.Count131072.C015824.packed 128 cuts15824 = true := by
 decide +kernel
def pointBounds15824 : List (Nat × Nat × Nat) := [(2078054400,96970129303841,96970507798394),(2078119936,96970543777836,96970922272662)]
theorem point_links_checked15824 : (cuts15824.take 2).map (fun c => (2078015489-1+2*2^9*c.k,96969878175042+c.lower,96970256669433+c.upper)) = pointBounds15824 := by
 decide +kernel
def cuts15825 : List PrefixCut := [⟨38,251112987,251113151⟩,
⟨102,671655685,671656119⟩,
⟨128,839869034,839869575⟩]
theorem checked15825 : checkPrefixCuts (2^48) 2078146561 9 Manual.Count131072.C015825.packed 128 cuts15825 = true := by
 decide +kernel
def pointBounds15825 : List (Nat × Nat × Nat) := [(2078185472,96970962437543,96971340932640),(2078251008,96971382980241,96971761475608)]
theorem point_links_checked15825 : (cuts15825.take 2).map (fun c => (2078146561-1+2*2^9*c.k,96970711324556+c.lower,96971089819489+c.upper)) = pointBounds15825 := by
 decide +kernel
def cuts15826 : List PrefixCut := [⟨38,247711241,247711400⟩,
⟨102,661862075,661862500⟩,
⟨128,830606536,830607069⟩]
theorem checked15826 : checkPrefixCuts (2^48) 2078277633 9 Manual.Count131072.C015826.packed 128 cuts15826 = true := by
 decide +kernel
def pointBounds15826 : List (Nat × Nat × Nat) := [(2078316544,96971798904831,96972177400464),(2078382080,96972213055665,96972591551564)]
theorem point_links_checked15826 : (cuts15826.take 2).map (fun c => (2078277633-1+2*2^9*c.k,96971551193590+c.lower,96971929689064+c.upper)) = pointBounds15826 := by
 decide +kernel
def cuts15827 : List PrefixCut := [⟨38,238215770,238215923⟩,
⟨102,653288492,653288911⟩,
⟨128,822022329,822022857⟩]
theorem checked15827 : checkPrefixCuts (2^48) 2078408705 9 Manual.Count131072.C015827.packed 128 cuts15827 = true := by
 decide +kernel
def pointBounds15827 : List (Nat × Nat × Nat) := [(2078447616,96972620015896,96972998512056),(2078513152,96973035088618,96973413585044)]
theorem point_links_checked15827 : (cuts15827.take 2).map (fun c => (2078408705-1+2*2^9*c.k,96972381800126+c.lower,96972760296133+c.upper)) = pointBounds15827 := by
 decide +kernel
def cuts15828 : List PrefixCut := [⟨38,251065483,251065647⟩,
⟨102,674913990,674914430⟩,
⟨128,847293295,847293847⟩]
theorem checked15828 : checkPrefixCuts (2^48) 2078539777 9 Manual.Count131072.C015828.packed 128 cuts15828 = true := by
 decide +kernel
def pointBounds15828 : List (Nat × Nat × Nat) := [(2078578688,96973454887938,96973833384637),(2078644224,96973878736445,96974257233420)]
theorem point_links_checked15828 : (cuts15828.take 2).map (fun c => (2078539777-1+2*2^9*c.k,96973203822455+c.lower,96973582318990+c.upper)) = pointBounds15828 := by
 decide +kernel
def cuts15829 : List PrefixCut := [⟨38,244685389,244685547⟩,
⟨102,666205311,666205746⟩,
⟨128,834105405,834105951⟩]
theorem checked15829 : checkPrefixCuts (2^48) 2078670849 9 Manual.Count131072.C015829.packed 128 cuts15829 = true := by
 decide +kernel
def pointBounds15829 : List (Nat × Nat × Nat) := [(2078709760,96974295801139,96974674298384),(2078775296,96974717321061,96975095818583)]
theorem point_links_checked15829 : (cuts15829.take 2).map (fun c => (2078670849-1+2*2^9*c.k,96974051115750+c.lower,96974429612837+c.upper)) = pointBounds15829 := by
 decide +kernel
def cuts15830 : List PrefixCut := [⟨38,241691146,241691302⟩,
⟨102,651811003,651811423⟩,
⟨128,817398816,817399342⟩]
theorem checked15830 : checkPrefixCuts (2^48) 2078801921 9 Manual.Count131072.C015830.packed 128 cuts15830 = true := by
 decide +kernel
def pointBounds15830 : List (Nat × Nat × Nat) := [(2078840832,96975126912301,96975505410090),(2078906368,96975537032158,96975915530211)]
theorem point_links_checked15830 : (cuts15830.take 2).map (fun c => (2078801921-1+2*2^9*c.k,96974885221155+c.lower,96975263718788+c.upper)) = pointBounds15830 := by
 decide +kernel
def cuts15831 : List PrefixCut := [⟨38,246008428,246008586⟩,
⟨102,660299561,660299985⟩,
⟨128,824658464,824658992⟩]
theorem checked15831 : checkPrefixCuts (2^48) 2078932993 9 Manual.Count131072.C015831.packed 128 cuts15831 = true := by
 decide +kernel
def pointBounds15831 : List (Nat × Nat × Nat) := [(2078971904,96975948628399,96976327126716),(2079037440,96976362919532,96976741418115)]
theorem point_links_checked15831 : (cuts15831.take 2).map (fun c => (2078932993-1+2*2^9*c.k,96975702619971+c.lower,96976081118130+c.upper)) = pointBounds15831 := by
 decide +kernel
def cuts15832 : List PrefixCut := [⟨38,244503708,244503864⟩,
⟨102,659987006,659987432⟩,
⟨128,825012440,825012976⟩]
theorem checked15832 : checkPrefixCuts (2^48) 2079064065 9 Manual.Count131072.C015832.packed 128 cuts15832 = true := by
 decide +kernel
def pointBounds15832 : List (Nat × Nat × Nat) := [(2079102976,96976771782143,96977150280986),(2079168512,96977187265441,96977565764554)]
theorem point_links_checked15832 : (cuts15832.take 2).map (fun c => (2079064065-1+2*2^9*c.k,96976527278435+c.lower,96976905777122+c.upper)) = pointBounds15832 := by
 decide +kernel
def cuts15833 : List PrefixCut := [⟨38,241916110,241916266⟩,
⟨102,658591626,658592052⟩,
⟨128,827803133,827803667⟩]
theorem checked15833 : checkPrefixCuts (2^48) 2079195137 9 Manual.Count131072.C015833.packed 128 cuts15833 = true := by
 decide +kernel
def pointBounds15833 : List (Nat × Nat × Nat) := [(2079234048,96977594206985,96977972706364),(2079299584,96978010882501,96978389382150)]
theorem point_links_checked15833 : (cuts15833.take 2).map (fun c => (2079195137-1+2*2^9*c.k,96977352290875+c.lower,96977730790098+c.upper)) = pointBounds15833 := by
 decide +kernel
def cuts15834 : List PrefixCut := [⟨38,243254606,243254765⟩,
⟨102,660851501,660851928⟩,
⟨128,827074372,827074910⟩]
theorem checked15834 : checkPrefixCuts (2^48) 2079326209 9 Manual.Count131072.C015834.packed 128 cuts15834 = true := by
 decide +kernel
def pointBounds15834 : List (Nat × Nat × Nat) := [(2079365120,96978423348614,96978801848530),(2079430656,96978840945509,96979219445693)]
theorem point_links_checked15834 : (cuts15834.take 2).map (fun c => (2079326209-1+2*2^9*c.k,96978180094008+c.lower,96978558593765+c.upper)) = pointBounds15834 := by
 decide +kernel
def cuts15835 : List PrefixCut := [⟨38,244728173,244728328⟩,
⟨102,659185524,659185945⟩,
⟨128,827563548,827564078⟩]
theorem checked15835 : checkPrefixCuts (2^48) 2079457281 9 Manual.Count131072.C015835.packed 128 cuts15835 = true := by
 decide +kernel
def pointBounds15835 : List (Nat × Nat × Nat) := [(2079496192,96979251896553,96979630397003),(2079561728,96979666353904,96980044854620)]
theorem point_links_checked15835 : (cuts15835.take 2).map (fun c => (2079457281-1+2*2^9*c.k,96979007168380+c.lower,96979385668675+c.upper)) = pointBounds15835 := by
 decide +kernel
def cuts15836 : List PrefixCut := [⟨38,244036018,244036175⟩,
⟨102,656707701,656708130⟩,
⟨128,822774300,822774836⟩]
theorem checked15836 : checkPrefixCuts (2^48) 2079588353 9 Manual.Count131072.C015836.packed 128 cuts15836 = true := by
 decide +kernel
def pointBounds15836 : List (Nat × Nat × Nat) := [(2079627264,96980078767946,96980457268928),(2079692800,96980491439629,96980869940883)]
theorem point_links_checked15836 : (cuts15836.take 2).map (fun c => (2079588353-1+2*2^9*c.k,96979834731928+c.lower,96980213232753+c.upper)) = pointBounds15836 := by
 decide +kernel
def cuts15837 : List PrefixCut := [⟨38,243073276,243073432⟩,
⟨102,658290495,658290918⟩,
⟨128,825158627,825159160⟩]
theorem checked15837 : checkPrefixCuts (2^48) 2079719425 9 Manual.Count131072.C015837.packed 128 cuts15837 = true := by
 decide +kernel
def pointBounds15837 : List (Nat × Nat × Nat) := [(2079758336,96980900579504,96981279081021),(2079823872,96981315796723,96981694298507)]
theorem point_links_checked15837 : (cuts15837.take 2).map (fun c => (2079719425-1+2*2^9*c.k,96980657506228+c.lower,96981036007589+c.upper)) = pointBounds15837 := by
 decide +kernel
def cuts15838 : List PrefixCut := [⟨38,249283225,249283387⟩,
⟨102,660820250,660820681⟩,
⟨128,834850157,834850701⟩]
theorem checked15838 : checkPrefixCuts (2^48) 2079850497 9 Manual.Count131072.C015838.packed 128 cuts15838 = true := by
 decide +kernel
def pointBounds15838 : List (Nat × Nat × Nat) := [(2079889408,96981731948080,96982110450136),(2079954944,96982143485105,96982521987430)]
theorem point_links_checked15838 : (cuts15838.take 2).map (fun c => (2079850497-1+2*2^9*c.k,96981482664855+c.lower,96981861166749+c.upper)) = pointBounds15838 := by
 decide +kernel
def cuts15839 : List PrefixCut := [⟨38,241012741,241012899⟩,
⟨102,646975761,646976183⟩,
⟨128,813958163,813958695⟩]
theorem checked15839 : checkPrefixCuts (2^48) 2079981569 9 Manual.Count131072.C015839.packed 128 cuts15839 = true := by
 decide +kernel
def pointBounds15839 : List (Nat × Nat × Nat) := [(2080020480,96982558527753,96982937030349),(2080086016,96982964490773,96983342993633)]
theorem point_links_checked15839 : (cuts15839.take 2).map (fun c => (2079981569-1+2*2^9*c.k,96982317515012+c.lower,96982696017450+c.upper)) = pointBounds15839 := by
 decide +kernel
def cuts15840 : List PrefixCut := [⟨38,247627999,247628160⟩,
⟨102,668314482,668314914⟩,
⟨128,840428138,840428681⟩]
theorem checked15840 : checkPrefixCuts (2^48) 2080112641 9 Manual.Count131072.C015840.packed 128 cuts15840 = true := by
 decide +kernel
def pointBounds15840 : List (Nat × Nat × Nat) := [(2080151552,96983379101174,96983757604305),(2080217088,96983799787657,96984178291059)]
theorem point_links_checked15840 : (cuts15840.take 2).map (fun c => (2080112641-1+2*2^9*c.k,96983131473175+c.lower,96983509976145+c.upper)) = pointBounds15840 := by
 decide +kernel
def cuts15841 : List PrefixCut := [⟨38,246259373,246259530⟩,
⟨102,658801091,658801519⟩,
⟨128,829280312,829280845⟩]
theorem checked15841 : checkPrefixCuts (2^48) 2080243713 9 Manual.Count131072.C015841.packed 128 cuts15841 = true := by
 decide +kernel
def pointBounds15841 : List (Nat × Nat × Nat) := [(2080282624,96984218160686,96984596664356),(2080348160,96984630702404,96985009206345)]
theorem point_links_checked15841 : (cuts15841.take 2).map (fun c => (2080243713-1+2*2^9*c.k,96983971901313+c.lower,96984350404826+c.upper)) = pointBounds15841 := by
 decide +kernel
def cuts15842 : List PrefixCut := [⟨38,241778975,241779133⟩,
⟨102,650100567,650100986⟩,
⟨128,815698500,815699027⟩]
theorem checked15842 : checkPrefixCuts (2^48) 2080374785 9 Manual.Count131072.C015842.packed 128 cuts15842 = true := by
 decide +kernel
def pointBounds15842 : List (Nat × Nat × Nat) := [(2080413696,96985042960600,96985421464804),(2080479232,96985451282192,96985829786657)]
theorem point_links_checked15842 : (cuts15842.take 2).map (fun c => (2080374785-1+2*2^9*c.k,96984801181625+c.lower,96985179685671+c.upper)) = pointBounds15842 := by
 decide +kernel
def cuts15843 : List PrefixCut := [⟨38,240816721,240816876⟩,
⟨102,654524087,654524510⟩,
⟨128,822411387,822411924⟩]
theorem checked15843 : checkPrefixCuts (2^48) 2080505857 9 Manual.Count131072.C015843.packed 128 cuts15843 = true := by
 decide +kernel
def pointBounds15843 : List (Nat × Nat × Nat) := [(2080544768,96985857696846,96986236201574),(2080610304,96986271404212,96986649909208)]
theorem point_links_checked15843 : (cuts15843.take 2).map (fun c => (2080505857-1+2*2^9*c.k,96985616880125+c.lower,96985995384698+c.upper)) = pointBounds15843 := by
 decide +kernel
def cuts15844 : List PrefixCut := [⟨38,241613252,241613413⟩,
⟨102,656647390,656647816⟩,
⟨128,831017359,831017893⟩]
theorem checked15844 : checkPrefixCuts (2^48) 2080636929 9 Manual.Count131072.C015844.packed 128 cuts15844 = true := by
 decide +kernel
def pointBounds15844 : List (Nat × Nat × Nat) := [(2080675840,96986680904764,96987059410035),(2080741376,96987095938902,96987474444438)]
theorem point_links_checked15844 : (cuts15844.take 2).map (fun c => (2080636929-1+2*2^9*c.k,96986439291512+c.lower,96986817796622+c.upper)) = pointBounds15844 := by
 decide +kernel
def cuts15845 : List PrefixCut := [⟨38,242815440,242815598⟩,
⟨102,649571912,649572335⟩,
⟨128,817438097,817438628⟩]
theorem checked15845 : checkPrefixCuts (2^48) 2080768001 9 Manual.Count131072.C015845.packed 128 cuts15845 = true := by
 decide +kernel
def pointBounds15845 : List (Nat × Nat × Nat) := [(2080806912,96987513124311,96987891630113),(2080872448,96987919880783,96988298386850)]
theorem point_links_checked15845 : (cuts15845.take 2).map (fun c => (2080768001-1+2*2^9*c.k,96987270308871+c.lower,96987648814515+c.upper)) = pointBounds15845 := by
 decide +kernel
def cuts15846 : List PrefixCut := [⟨38,251862880,251863043⟩,
⟨102,662380979,662381408⟩,
⟨128,829830819,829831355⟩]
theorem checked15846 : checkPrefixCuts (2^48) 2080899073 9 Manual.Count131072.C015846.packed 128 cuts15846 = true := by
 decide +kernel
def pointBounds15846 : List (Nat × Nat × Nat) := [(2080937984,96988339609848,96988718116186),(2081003520,96988750127947,96989128634551)]
theorem point_links_checked15846 : (cuts15846.take 2).map (fun c => (2080899073-1+2*2^9*c.k,96988087746968+c.lower,96988466253143+c.upper)) = pointBounds15846 := by
 decide +kernel
def cuts15847 : List PrefixCut := [⟨38,235481071,235481225⟩,
⟨102,650301436,650301855⟩,
⟨128,819228483,819229013⟩]
theorem checked15847 : checkPrefixCuts (2^48) 2081030145 9 Manual.Count131072.C015847.packed 128 cuts15847 = true := by
 decide +kernel
def pointBounds15847 : List (Nat × Nat × Nat) := [(2081069056,96989153058858,96989531565723),(2081134592,96989567879223,96989946386353)]
theorem point_links_checked15847 : (cuts15847.take 2).map (fun c => (2081030145-1+2*2^9*c.k,96988917577787+c.lower,96989296084498+c.upper)) = pointBounds15847 := by
 decide +kernel
def cuts15848 : List PrefixCut := [⟨38,246286068,246286226⟩,
⟨102,660539326,660539752⟩,
⟨128,827021382,827021918⟩]
theorem checked15848 : checkPrefixCuts (2^48) 2081161217 9 Manual.Count131072.C015848.packed 128 cuts15848 = true := by
 decide +kernel
def pointBounds15848 : List (Nat × Nat × Nat) := [(2081200128,96989983092338,96990361599737),(2081265664,96990397345596,96990775853263)]
theorem point_links_checked15848 : (cuts15848.take 2).map (fun c => (2081161217-1+2*2^9*c.k,96989736806270+c.lower,96990115313511+c.upper)) = pointBounds15848 := by
 decide +kernel
def cuts15849 : List PrefixCut := [⟨38,246135279,246135438⟩,
⟨102,665771933,665772372⟩,
⟨128,837247145,837247696⟩]
theorem checked15849 : checkPrefixCuts (2^48) 2081292289 9 Manual.Count131072.C015849.packed 128 cuts15849 = true := by
 decide +kernel
def pointBounds15849 : List (Nat × Nat × Nat) := [(2081331200,96990809962931,96991188470867),(2081396736,96991229599585,96991608107801)]
theorem point_links_checked15849 : (cuts15849.take 2).map (fun c => (2081292289-1+2*2^9*c.k,96990563827652+c.lower,96990942335429+c.upper)) = pointBounds15849 := by
 decide +kernel
def cuts15850 : List PrefixCut := [⟨38,241386771,241386928⟩,
⟨102,668028891,668029323⟩,
⟨128,834760416,834760955⟩]
theorem checked15850 : checkPrefixCuts (2^48) 2081423361 9 Manual.Count131072.C015850.packed 128 cuts15850 = true := by
 decide +kernel
def pointBounds15850 : List (Nat × Nat × Nat) := [(2081462272,96991642461568,96992020970053),(2081527808,96992069103688,96992447612448)]
theorem point_links_checked15850 : (cuts15850.take 2).map (fun c => (2081423361-1+2*2^9*c.k,96991401074797+c.lower,96991779583125+c.upper)) = pointBounds15850 := by
 decide +kernel
def cuts15851 : List PrefixCut := [⟨38,240154550,240154707⟩,
⟨102,654329585,654330014⟩,
⟨128,822537998,822538538⟩]
theorem checked15851 : checkPrefixCuts (2^48) 2081554433 9 Manual.Count131072.C015851.packed 128 cuts15851 = true := by
 decide +kernel
def pointBounds15851 : List (Nat × Nat × Nat) := [(2081593344,96992475989763,96992854498787),(2081658880,96992890164798,96993268674094)]
theorem point_links_checked15851 : (cuts15851.take 2).map (fun c => (2081554433-1+2*2^9*c.k,96992235835213+c.lower,96992614344080+c.upper)) = pointBounds15851 := by
 decide +kernel
def cuts15852 : List PrefixCut := [⟨38,248387419,248387577⟩,
⟨102,655775862,655776286⟩,
⟨128,824920122,824920655⟩]
theorem checked15852 : checkPrefixCuts (2^48) 2081685505 9 Manual.Count131072.C015852.packed 128 cuts15852 = true := by
 decide +kernel
def pointBounds15852 : List (Nat × Nat × Nat) := [(2081724416,96993306760630,96993685270195),(2081789952,96993714149073,96994092658904)]
theorem point_links_checked15852 : (cuts15852.take 2).map (fun c => (2081685505-1+2*2^9*c.k,96993058373211+c.lower,96993436882618+c.upper)) = pointBounds15852 := by
 decide +kernel
def cuts15853 : List PrefixCut := [⟨38,252157570,252157729⟩,
⟨102,658709265,658709692⟩,
⟨128,828383703,828384243⟩]
theorem checked15853 : checkPrefixCuts (2^48) 2081816577 9 Manual.Count131072.C015853.packed 128 cuts15853 = true := by
 decide +kernel
def pointBounds15853 : List (Nat × Nat × Nat) := [(2081855488,96994135450903,96994513961002),(2081921024,96994542002598,96994920512965)]
theorem point_links_checked15853 : (cuts15853.take 2).map (fun c => (2081816577-1+2*2^9*c.k,96993883293333+c.lower,96994261803273+c.upper)) = pointBounds15853 := by
 decide +kernel
def cuts15854 : List PrefixCut := [⟨38,244435437,244435598⟩,
⟨102,656504319,656504754⟩,
⟨128,824140189,824140731⟩]
theorem checked15854 : checkPrefixCuts (2^48) 2081947649 9 Manual.Count131072.C015854.packed 128 cuts15854 = true := by
 decide +kernel
def pointBounds15854 : List (Nat × Nat × Nat) := [(2081986560,96994956112473,96995334623114),(2082052096,96995368181355,96995746692270)]
theorem point_links_checked15854 : (cuts15854.take 2).map (fun c => (2081947649-1+2*2^9*c.k,96994711677036+c.lower,96995090187516+c.upper)) = pointBounds15854 := by
 decide +kernel
def cuts15855 : List PrefixCut := [⟨38,243068207,243068365⟩,
⟨102,661870385,661870816⟩,
⟨128,828684635,828685173⟩]
theorem checked15855 : checkPrefixCuts (2^48) 2082078721 9 Manual.Count131072.C015855.packed 128 cuts15855 = true := by
 decide +kernel
def pointBounds15855 : List (Nat × Nat × Nat) := [(2082117632,96995778885432,96996157396612),(2082183168,96996197687610,96996576199063)]
theorem point_links_checked15855 : (cuts15855.take 2).map (fun c => (2082078721-1+2*2^9*c.k,96995535817225+c.lower,96995914328247+c.upper)) = pointBounds15855 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000182
