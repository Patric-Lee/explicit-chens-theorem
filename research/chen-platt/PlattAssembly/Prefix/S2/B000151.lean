import PlattAssemblyKernel
import PlattCertificates.Count131072.C014832
import PlattCertificates.Count131072.C014833
import PlattCertificates.Count131072.C014834
import PlattCertificates.Count131072.C014835
import PlattCertificates.Count131072.C014836
import PlattCertificates.Count131072.C014837
import PlattCertificates.Count131072.C014838
import PlattCertificates.Count131072.C014839
import PlattCertificates.Count131072.C014840
import PlattCertificates.Count131072.C014841
import PlattCertificates.Count131072.C014842
import PlattCertificates.Count131072.C014843
import PlattCertificates.Count131072.C014844
import PlattCertificates.Count131072.C014845
import PlattCertificates.Count131072.C014846
import PlattCertificates.Count131072.C014847
import PlattCertificates.Count131072.C014848
import PlattCertificates.Count131072.C014849
import PlattCertificates.Count131072.C014850
import PlattCertificates.Count131072.C014851
import PlattCertificates.Count131072.C014852
import PlattCertificates.Count131072.C014853
import PlattCertificates.Count131072.C014854
import PlattCertificates.Count131072.C014855
import PlattCertificates.Count131072.C014856
import PlattCertificates.Count131072.C014857
import PlattCertificates.Count131072.C014858
import PlattCertificates.Count131072.C014859
import PlattCertificates.Count131072.C014860
import PlattCertificates.Count131072.C014861
import PlattCertificates.Count131072.C014862
import PlattCertificates.Count131072.C014863
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000151
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts14832 : List PrefixCut := [⟨42,297222706,297222901⟩,
⟨102,701648570,701649041⟩,
⟨128,876765758,876766346⟩]
theorem checked14832 : checkPrefixCuts (2^48) 1947992065 9 Manual.Count131072.C014832.packed 128 cuts14832 = true := by
 decide +kernel
def pointBounds14832 : List (Nat × Nat × Nat) := [(1948035072,96121181167930,96121559103312),(1948096512,96121585593794,96121963529452)]
theorem point_links_checked14832 : (cuts14832.take 2).map (fun c => (1947992065-1+2*2^9*c.k,96120883945224+c.lower,96121261880411+c.upper)) = pointBounds14832 := by
 decide +kernel
def cuts14833 : List PrefixCut := [⟨34,237098059,237098216⟩,
⟨94,650600595,650601035⟩,
⟨128,883352621,883353219⟩]
theorem checked14833 : checkPrefixCuts (2^48) 1948123137 9 Manual.Count131072.C014833.packed 128 cuts14833 = true := by
 decide +kernel
def pointBounds14833 : List (Nat × Nat × Nat) := [(1948157952,96121997809041,96122375744973),(1948219392,96122411311577,96122789247792)]
theorem point_links_checked14833 : (cuts14833.take 2).map (fun c => (1948123137-1+2*2^9*c.k,96121760710982+c.lower,96122138646757+c.upper)) = pointBounds14833 := by
 decide +kernel
def cuts14834 : List PrefixCut := [⟨26,182037822,182037942⟩,
⟨86,591469140,591469538⟩,
⟨128,886471412,886472004⟩]
theorem checked14834 : checkPrefixCuts (2^48) 1948254209 9 Manual.Count131072.C014834.packed 128 cuts14834 = true := by
 decide +kernel
def pointBounds14834 : List (Nat × Nat × Nat) := [(1948280832,96122826101425,96123204037918),(1948342272,96123235532743,96123613469514)]
theorem point_links_checked14834 : (cuts14834.take 2).map (fun c => (1948254209-1+2*2^9*c.k,96122644063603+c.lower,96123021999976+c.upper)) = pointBounds14834 := by
 decide +kernel
def cuts14835 : List PrefixCut := [⟨18,128862803,128862888⟩,
⟨78,551847783,551848148⟩,
⟨128,898546729,898547325⟩]
theorem checked14835 : checkPrefixCuts (2^48) 1948385281 9 Manual.Count131072.C014835.packed 128 cuts14835 = true := by
 decide +kernel
def pointBounds14835 : List (Nat × Nat × Nat) := [(1948403712,96123659397818,96124037334868),(1948465152,96124082382798,96124460320128)]
theorem point_links_checked14835 : (cuts14835.take 2).map (fun c => (1948385281-1+2*2^9*c.k,96123530535015+c.lower,96123908471980+c.upper)) = pointBounds14835 := by
 decide +kernel
def cuts14836 : List PrefixCut := [⟨10,64427210,64427256⟩,
⟨70,478429408,478429730⟩,
⟨128,872340438,872341022⟩]
theorem checked14836 : checkPrefixCuts (2^48) 1948516353 9 Manual.Count131072.C014836.packed 128 cuts14836 = true := by
 decide +kernel
def pointBounds14836 : List (Nat × Nat × Nat) := [(1948526592,96124493508954,96124871446561),(1948588032,96124907511152,96125285449035)]
theorem point_links_checked14836 : (cuts14836.take 2).map (fun c => (1948516353-1+2*2^9*c.k,96124429081744+c.lower,96124807019305+c.upper)) = pointBounds14836 := by
 decide +kernel
def cuts14837 : List PrefixCut := [⟨2,14589067,14589077⟩,
⟨62,424954114,424954395⟩,
⟨122,835161785,835162346⟩,
⟨128,870693236,870693822⟩]
theorem checked14837 : checkPrefixCuts (2^48) 1948647425 9 Manual.Count131072.C014837.packed 128 cuts14837 = true := by
 decide +kernel
def pointBounds14837 : List (Nat × Nat × Nat) := [(1948649472,96125316011249,96125693949404),(1948710912,96125726376296,96126104314722),(1948772352,96126136583967,96126514522673)]
theorem point_links_checked14837 : (cuts14837.take 3).map (fun c => (1948647425-1+2*2^9*c.k,96125301422182+c.lower,96125679360327+c.upper)) = pointBounds14837 := by
 decide +kernel
def cuts14838 : List PrefixCut := [⟨54,378418441,378418692⟩,
⟨114,785422667,785423190⟩,
⟨128,878000619,878001206⟩]
theorem checked14838 : checkPrefixCuts (2^48) 1948778497 9 Manual.Count131072.C014838.packed 128 cuts14838 = true := by
 decide +kernel
def pointBounds14838 : List (Nat × Nat × Nat) := [(1948833792,96126550533859,96126928472841),(1948895232,96126957538085,96127335477339)]
theorem point_links_checked14838 : (cuts14838.take 2).map (fun c => (1948778497-1+2*2^9*c.k,96126172115418+c.lower,96126550054149+c.upper)) = pointBounds14838 := by
 decide +kernel
def cuts14839 : List PrefixCut := [⟨46,324812099,324812314⟩,
⟨106,729046682,729047167⟩,
⟨128,881118801,881119388⟩]
theorem checked14839 : checkPrefixCuts (2^48) 1948909569 9 Manual.Count131072.C014839.packed 128 cuts14839 = true := by
 decide +kernel
def pointBounds14839 : List (Nat × Nat × Nat) := [(1948956672,96127374928136,96127752867669),(1949018112,96127779162719,96128157102522)]
theorem point_links_checked14839 : (cuts14839.take 2).map (fun c => (1948909569-1+2*2^9*c.k,96127050116037+c.lower,96127428055355+c.upper)) = pointBounds14839 := by
 decide +kernel
def cuts14840 : List PrefixCut := [⟨38,265002829,265003006⟩,
⟨98,678743252,678743710⟩,
⟨128,885825130,885825725⟩]
theorem checked14840 : checkPrefixCuts (2^48) 1949040641 9 Manual.Count131072.C014840.packed 128 cuts14840 = true := by
 decide +kernel
def pointBounds14840 : List (Nat × Nat × Nat) := [(1949079552,96128196237667,96128574177749),(1949140992,96128609978090,96128987918453)]
theorem point_links_checked14840 : (cuts14840.take 2).map (fun c => (1949040641-1+2*2^9*c.k,96127931234838+c.lower,96128309174743+c.upper)) = pointBounds14840 := by
 decide +kernel
def cuts14841 : List PrefixCut := [⟨30,203324084,203324218⟩,
⟨90,627002151,627002572⟩,
⟨128,896884217,896884822⟩]
theorem checked14841 : checkPrefixCuts (2^48) 1949171713 9 Manual.Count131072.C014841.packed 128 cuts14841 = true := by
 decide +kernel
def pointBounds14841 : List (Nat × Nat × Nat) := [(1949202432,96129020384052,96129398324686),(1949263872,96129444062119,96129822003040)]
theorem point_links_checked14841 : (cuts14841.take 2).map (fun c => (1949171713-1+2*2^9*c.k,96128817059968+c.lower,96129195000468+c.upper)) = pointBounds14841 := by
 decide +kernel
def cuts14842 : List PrefixCut := [⟨22,152049925,152050027⟩,
⟨82,566171247,566171624⟩,
⟨128,891625761,891626355⟩]
theorem checked14842 : checkPrefixCuts (2^48) 1949302785 9 Manual.Count131072.C014842.packed 128 cuts14842 = true := by
 decide +kernel
def pointBounds14842 : List (Nat × Nat × Nat) := [(1949325312,96129865994110,96130243935317),(1949386752,96130280115432,96130658056914)]
theorem point_links_checked14842 : (cuts14842.take 2).map (fun c => (1949302785-1+2*2^9*c.k,96129713944185+c.lower,96130091885290+c.upper)) = pointBounds14842 := by
 decide +kernel
def cuts14843 : List PrefixCut := [⟨14,96162073,96162139⟩,
⟨74,507947175,507947517⟩,
⟨128,882036637,882037231⟩]
theorem checked14843 : checkPrefixCuts (2^48) 1949433857 9 Manual.Count131072.C014843.packed 128 cuts14843 = true := by
 decide +kernel
def pointBounds14843 : List (Nat × Nat × Nat) := [(1949448192,96130701732019,96131079673784),(1949509632,96131113517121,96131491459162)]
theorem point_links_checked14843 : (cuts14843.take 2).map (fun c => (1949433857-1+2*2^9*c.k,96130605569946+c.lower,96130983511645+c.upper)) = pointBounds14843 := by
 decide +kernel
def cuts14844 : List PrefixCut := [⟨6,42014023,42014051⟩,
⟨66,457093795,457094096⟩,
⟨126,880245244,880245826⟩,
⟨128,892949687,892950278⟩]
theorem checked14844 : checkPrefixCuts (2^48) 1949564929 9 Manual.Count131072.C014844.packed 128 cuts14844 = true := by
 decide +kernel
def pointBounds14844 : List (Nat × Nat × Nat) := [(1949571072,96131529620606,96131907562927),(1949632512,96131944700378,96132322642972),(1949693952,96132367851827,96132745794702)]
theorem point_links_checked14844 : (cuts14844.take 3).map (fun c => (1949564929-1+2*2^9*c.k,96131487606583+c.lower,96131865548876+c.upper)) = pointBounds14844 := by
 decide +kernel
def cuts14845 : List PrefixCut := [⟨58,402349168,402349436⟩,
⟨118,819555144,819555694⟩,
⟨128,887837079,887837675⟩]
theorem checked14845 : checkPrefixCuts (2^48) 1949696001 9 Manual.Count131072.C014845.packed 128 cuts14845 = true := by
 decide +kernel
def pointBounds14845 : List (Nat × Nat × Nat) := [(1949755392,96132782905438,96133160848590),(1949816832,96133200111414,96133578054848)]
theorem point_links_checked14845 : (cuts14845.take 2).map (fun c => (1949696001-1+2*2^9*c.k,96132380556270+c.lower,96132758499154+c.upper)) = pointBounds14845 := by
 decide +kernel
def cuts14846 : List PrefixCut := [⟨50,346601085,346601313⟩,
⟨110,752954244,752954741⟩,
⟨128,878249942,878250525⟩]
theorem checked14846 : checkPrefixCuts (2^48) 1949827073 9 Manual.Count131072.C014846.packed 128 cuts14846 = true := by
 decide +kernel
def pointBounds14846 : List (Nat × Nat × Nat) := [(1949878272,96133614994434,96133992938142),(1949939712,96134021347593,96134399291570)]
theorem point_links_checked14846 : (cuts14846.take 2).map (fun c => (1949827073-1+2*2^9*c.k,96133268393349+c.lower,96133646336829+c.upper)) = pointBounds14846 := by
 decide +kernel
def cuts14847 : List PrefixCut := [⟨42,286529974,286530161⟩,
⟨102,700074757,700075222⟩,
⟨128,881222054,881222639⟩]
theorem checked14847 : checkPrefixCuts (2^48) 1949958145 9 Manual.Count131072.C014847.packed 128 cuts14847 = true := by
 decide +kernel
def pointBounds14847 : List (Nat × Nat × Nat) := [(1950001152,96134433173265,96134811117515),(1950062592,96134846718048,96135224662576)]
theorem point_links_checked14847 : (cuts14847.take 2).map (fun c => (1949958145-1+2*2^9*c.k,96134146643291+c.lower,96134524587354+c.upper)) = pointBounds14847 := by
 decide +kernel
def cuts14848 : List PrefixCut := [⟨34,232817531,232817688⟩,
⟨94,654707653,654708091⟩,
⟨128,890833301,890833894⟩]
theorem checked14848 : checkPrefixCuts (2^48) 1950089217 9 Manual.Count131072.C014848.packed 128 cuts14848 = true := by
 decide +kernel
def pointBounds14848 : List (Nat × Nat × Nat) := [(1950124032,96135260682876,96135638627681),(1950185472,96135682572998,96136060518084)]
theorem point_links_checked14848 : (cuts14848.take 2).map (fun c => (1950089217-1+2*2^9*c.k,96135027865345+c.lower,96135405809993+c.upper)) = pointBounds14848 := by
 decide +kernel
def cuts14849 : List PrefixCut := [⟨26,183153265,183153387⟩,
⟨86,598377803,598378201⟩,
⟨128,887309817,887310405⟩]
theorem checked14849 : checkPrefixCuts (2^48) 1950220289 9 Manual.Count131072.C014849.packed 128 cuts14849 = true := by
 decide +kernel
def pointBounds14849 : List (Nat × Nat × Nat) := [(1950246912,96136101851911,96136479797274),(1950308352,96136517076449,96136895022088)]
theorem point_links_checked14849 : (cuts14849.take 2).map (fun c => (1950220289-1+2*2^9*c.k,96135918698646+c.lower,96136296643887+c.upper)) = pointBounds14849 := by
 decide +kernel
def cuts14850 : List PrefixCut := [⟨18,126856753,126856836⟩,
⟨78,538447207,538447571⟩,
⟨128,884363768,884364364⟩]
theorem checked14850 : checkPrefixCuts (2^48) 1950351361 9 Manual.Count131072.C014850.packed 128 cuts14850 = true := by
 decide +kernel
def pointBounds14850 : List (Nat × Nat × Nat) := [(1950369792,96136932865216,96137310811128),(1950431232,96137344455670,96137722401863)]
theorem point_links_checked14850 : (cuts14850.take 2).map (fun c => (1950351361-1+2*2^9*c.k,96136806008463+c.lower,96137183954292+c.upper)) = pointBounds14850 := by
 decide +kernel
def cuts14851 : List PrefixCut := [⟨10,70567591,70567639⟩,
⟨70,488626090,488626422⟩,
⟨128,895560281,895560886⟩]
theorem checked14851 : checkPrefixCuts (2^48) 1950482433 9 Manual.Count131072.C014851.packed 128 cuts14851 = true := by
 decide +kernel
def pointBounds14851 : List (Nat × Nat × Nat) := [(1950492672,96137760939822,96138138886295),(1950554112,96138178998321,96138556945078)]
theorem point_links_checked14851 : (cuts14851.take 2).map (fun c => (1950482433-1+2*2^9*c.k,96137690372231+c.lower,96138068318656+c.upper)) = pointBounds14851 := by
 decide +kernel
def cuts14852 : List PrefixCut := [⟨2,14574362,14574372⟩,
⟨62,427123045,427123332⟩,
⟨122,845863485,845864053⟩,
⟨128,886265031,886265626⟩]
theorem checked14852 : checkPrefixCuts (2^48) 1950613505 9 Manual.Count131072.C014852.packed 128 cuts14852 = true := by
 decide +kernel
def pointBounds14852 : List (Nat × Nat × Nat) := [(1950615552,96138600506874,96138978453914),(1950676992,96139013055557,96139391002874),(1950738432,96139431795997,96139809743595)]
theorem point_links_checked14852 : (cuts14852.take 3).map (fun c => (1950613505-1+2*2^9*c.k,96138585932512+c.lower,96138963879542+c.upper)) = pointBounds14852 := by
 decide +kernel
def cuts14853 : List PrefixCut := [⟨54,378469966,378470220⟩,
⟨114,798915400,798915932⟩,
⟨128,898037010,898037606⟩]
theorem checked14853 : checkPrefixCuts (2^48) 1950744577 9 Manual.Count131072.C014853.packed 128 cuts14853 = true := by
 decide +kernel
def pointBounds14853 : List (Nat × Nat × Nat) := [(1950799872,96139850667509,96140228615388),(1950861312,96140271112943,96140649061100)]
theorem point_links_checked14853 : (cuts14853.take 2).map (fun c => (1950744577-1+2*2^9*c.k,96139472197543+c.lower,96139850145168+c.upper)) = pointBounds14853 := by
 decide +kernel
def cuts14854 : List PrefixCut := [⟨46,315106576,315106790⟩,
⟨106,730331586,730332080⟩,
⟨128,885424471,885425070⟩]
theorem checked14854 : checkPrefixCuts (2^48) 1950875649 9 Manual.Count131072.C014854.packed 128 cuts14854 = true := by
 decide +kernel
def pointBounds14854 : List (Nat × Nat × Nat) := [(1950922752,96140685341129,96141063289564),(1950984192,96141100566139,96141478514854)]
theorem point_links_checked14854 : (cuts14854.take 2).map (fun c => (1950875649-1+2*2^9*c.k,96140370234553+c.lower,96140748182774+c.upper)) = pointBounds14854 := by
 decide +kernel
def cuts14855 : List PrefixCut := [⟨38,264302971,264303149⟩,
⟨98,680223199,680223657⟩,
⟨128,885220965,885221557⟩]
theorem checked14855 : checkPrefixCuts (2^48) 1951006721 9 Manual.Count131072.C014855.packed 128 cuts14855 = true := by
 decide +kernel
def pointBounds14855 : List (Nat × Nat × Nat) := [(1951045632,96141519961995,96141897910993),(1951107072,96141935882223,96142313831501)]
theorem point_links_checked14855 : (cuts14855.take 2).map (fun c => (1951006721-1+2*2^9*c.k,96141255659024+c.lower,96141633607844+c.upper)) = pointBounds14855 := by
 decide +kernel
def cuts14856 : List PrefixCut := [⟨30,206437183,206437319⟩,
⟨90,617715042,617715451⟩,
⟨128,882276305,882276894⟩]
theorem checked14856 : checkPrefixCuts (2^48) 1951137793 9 Manual.Count131072.C014856.packed 128 cuts14856 = true := by
 decide +kernel
def pointBounds14856 : List (Nat × Nat × Nat) := [(1951168512,96142347317172,96142725266720),(1951229952,96142758595031,96143136544852)]
theorem point_links_checked14856 : (cuts14856.take 2).map (fun c => (1951137793-1+2*2^9*c.k,96142140879989+c.lower,96142518829401+c.upper)) = pointBounds14856 := by
 decide +kernel
def cuts14857 : List PrefixCut := [⟨22,152040970,152041068⟩,
⟨82,567331859,567332237⟩,
⟨128,881784349,881784941⟩]
theorem checked14857 : checkPrefixCuts (2^48) 1951268865 9 Manual.Count131072.C014857.packed 128 cuts14857 = true := by
 decide +kernel
def pointBounds14857 : List (Nat × Nat × Nat) := [(1951291392,96143175197264,96143553147363),(1951352832,96143590488153,96143968438532)]
theorem point_links_checked14857 : (cuts14857.take 2).map (fun c => (1951268865-1+2*2^9*c.k,96143023156294+c.lower,96143401106295+c.upper)) = pointBounds14857 := by
 decide +kernel
def cuts14858 : List PrefixCut := [⟨14,96497912,96497975⟩,
⟨74,507291228,507291563⟩,
⟨128,870330410,870330992⟩]
theorem checked14858 : checkPrefixCuts (2^48) 1951399937 9 Manual.Count131072.C014858.packed 128 cuts14858 = true := by
 decide +kernel
def pointBounds14858 : List (Nat × Nat × Nat) := [(1951414272,96144001438555,96144379389211),(1951475712,96144412231871,96144790182799)]
theorem point_links_checked14858 : (cuts14858.take 2).map (fun c => (1951399937-1+2*2^9*c.k,96143904940643+c.lower,96144282891236+c.upper)) = pointBounds14858 := by
 decide +kernel
def cuts14859 : List PrefixCut := [⟨6,39519735,39519762⟩,
⟨66,452739024,452739330⟩,
⟨126,865801083,865801666⟩,
⟨128,880223407,880224000⟩]
theorem checked14859 : checkPrefixCuts (2^48) 1951531009 9 Manual.Count131072.C014859.packed 128 cuts14859 = true := by
 decide +kernel
def pointBounds14859 : List (Nat × Nat × Nat) := [(1951537152,96144814790788,96145192741990),(1951598592,96145228010077,96145605961558),(1951660032,96145641072136,96146019023894)]
theorem point_links_checked14859 : (cuts14859.take 3).map (fun c => (1951531009-1+2*2^9*c.k,96144775271053+c.lower,96145153222228+c.upper)) = pointBounds14859 := by
 decide +kernel
def cuts14860 : List PrefixCut := [⟨58,395598171,395598436⟩,
⟨118,809499487,809500029⟩,
⟨128,880596919,880597508⟩]
theorem checked14860 : checkPrefixCuts (2^48) 1951662081 9 Manual.Count131072.C014860.packed 128 cuts14860 = true := by
 decide +kernel
def pointBounds14860 : List (Nat × Nat × Nat) := [(1951721472,96146051092631,96146429044664),(1951782912,96146464993947,96146842946257)]
theorem point_links_checked14860 : (cuts14860.take 2).map (fun c => (1951662081-1+2*2^9*c.k,96145655494460+c.lower,96146033446228+c.upper)) = pointBounds14860 := by
 decide +kernel
def cuts14861 : List PrefixCut := [⟨50,343512013,343512241⟩,
⟨110,767481916,767482424⟩,
⟨128,897842754,897843347⟩]
theorem checked14861 : checkPrefixCuts (2^48) 1951793153 9 Manual.Count131072.C014861.packed 128 cuts14861 = true := by
 decide +kernel
def pointBounds14861 : List (Nat × Nat × Nat) := [(1951844352,96146879603392,96147257555977),(1951905792,96147303573295,96147681526160)]
theorem point_links_checked14861 : (cuts14861.take 2).map (fun c => (1951793153-1+2*2^9*c.k,96146536091379+c.lower,96146914043736+c.upper)) = pointBounds14861 := by
 decide +kernel
def cuts14862 : List PrefixCut := [⟨42,282636331,282636523⟩,
⟨102,700811631,700812100⟩,
⟨128,881199682,881200273⟩]
theorem checked14862 : checkPrefixCuts (2^48) 1951924225 9 Manual.Count131072.C014862.packed 128 cuts14862 = true := by
 decide +kernel
def pointBounds14862 : List (Nat × Nat × Nat) := [(1951967232,96147716570464,96148094523606),(1952028672,96148134745764,96148512699183)]
theorem point_links_checked14862 : (cuts14862.take 2).map (fun c => (1951924225-1+2*2^9*c.k,96147433934133+c.lower,96147811887083+c.upper)) = pointBounds14862 := by
 decide +kernel
def cuts14863 : List PrefixCut := [⟨34,233592371,233592525⟩,
⟨94,652173757,652174187⟩,
⟨128,893108077,893108666⟩]
theorem checked14863 : checkPrefixCuts (2^48) 1952055297 9 Manual.Count131072.C014863.packed 128 cuts14863 = true := by
 decide +kernel
def pointBounds14863 : List (Nat × Nat × Nat) := [(1952090112,96148548726186,96148926679881),(1952151552,96148967307572,96149345261543)]
theorem point_links_checked14863 : (cuts14863.take 2).map (fun c => (1952055297-1+2*2^9*c.k,96148315133815+c.lower,96148693087356+c.upper)) = pointBounds14863 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000151
