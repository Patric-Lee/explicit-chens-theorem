import PlattAssemblyKernel
import PlattCertificates.Count131072.C021760
import PlattCertificates.Count131072.C021761
import PlattCertificates.Count131072.C021762
import PlattCertificates.Count131072.C021763
import PlattCertificates.Count131072.C021764
import PlattCertificates.Count131072.C021765
import PlattCertificates.Count131072.C021766
import PlattCertificates.Count131072.C021767
import PlattCertificates.Count131072.C021768
import PlattCertificates.Count131072.C021769
import PlattCertificates.Count131072.C021770
import PlattCertificates.Count131072.C021771
import PlattCertificates.Count131072.C021772
import PlattCertificates.Count131072.C021773
import PlattCertificates.Count131072.C021774
import PlattCertificates.Count131072.C021775
import PlattCertificates.Count131072.C021776
import PlattCertificates.Count131072.C021777
import PlattCertificates.Count131072.C021778
import PlattCertificates.Count131072.C021779
import PlattCertificates.Count131072.C021780
import PlattCertificates.Count131072.C021781
import PlattCertificates.Count131072.C021782
import PlattCertificates.Count131072.C021783
import PlattCertificates.Count131072.C021784
import PlattCertificates.Count131072.C021785
import PlattCertificates.Count131072.C021786
import PlattCertificates.Count131072.C021787
import PlattCertificates.Count131072.C021788
import PlattCertificates.Count131072.C021789
import PlattCertificates.Count131072.C021790
import PlattCertificates.Count131072.C021791
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000055
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts21760 : List PrefixCut := [⟨10,48586837,48586864⟩,
⟨98,461321350,461321613⟩,
⟨128,604612499,604612841⟩]
theorem checked21760 : checkPrefixCuts (2^48) 2856058881 9 Manual.Count131072.C021760.packed 128 cuts21760 = true := by
 decide +kernel
def pointBounds21760 : List (Nat × Nat × Nat) := [(2856069120,101111728490425,101112109493612),(2856159232,101112141224938,101112522228361)]
theorem point_links_checked21760 : (cuts21760.take 2).map (fun c => (2856058881-1+2*2^9*c.k,101111679903588+c.lower,101112060906748+c.upper)) = pointBounds21760 := by
 decide +kernel
def cuts21761 : List PrefixCut := [⟨58,271401351,271401509⟩,
⟨128,600150138,600150488⟩]
theorem checked21761 : checkPrefixCuts (2^48) 2856189953 9 Manual.Count131072.C021761.packed 128 cuts21761 = true := by
 decide +kernel
def pointBounds21761 : List (Nat × Nat × Nat) := [(2856249344,101112555917438,101112936921098)]
theorem point_links_checked21761 : (cuts21761.take 1).map (fun c => (2856189953-1+2*2^9*c.k,101112284516087+c.lower,101112665519589+c.upper)) = pointBounds21761 := by
 decide +kernel
def cuts21762 : List PrefixCut := [⟨18,85733485,85733535⟩,
⟨106,491333880,491334169⟩,
⟨128,592042194,592042541⟩]
theorem checked21762 : checkPrefixCuts (2^48) 2856321025 9 Manual.Count131072.C021762.packed 128 cuts21762 = true := by
 decide +kernel
def pointBounds21762 : List (Nat × Nat × Nat) := [(2856339456,101112970399710,101113351403612),(2856429568,101113376000105,101113757004246)]
theorem point_links_checked21762 : (cuts21762.take 2).map (fun c => (2856321025-1+2*2^9*c.k,101112884666225+c.lower,101113265670077+c.upper)) = pointBounds21762 := by
 decide +kernel
def cuts21763 : List PrefixCut := [⟨66,305667613,305667791⟩,
⟨128,604824702,604825051⟩]
theorem checked21763 : checkPrefixCuts (2^48) 2856452097 9 Manual.Count131072.C021763.packed 128 cuts21763 = true := by
 decide +kernel
def pointBounds21763 : List (Nat × Nat × Nat) := [(2856519680,101113782376032,101114163380409)]
theorem point_links_checked21763 : (cuts21763.take 1).map (fun c => (2856452097-1+2*2^9*c.k,101113476708419+c.lower,101113857712618+c.upper)) = pointBounds21763 := by
 decide +kernel
def cuts21764 : List PrefixCut := [⟨26,120902499,120902568⟩,
⟨114,519567234,519567519⟩,
⟨128,584105197,584105520⟩]
theorem checked21764 : checkPrefixCuts (2^48) 2856583169 9 Manual.Count131072.C021764.packed 128 cuts21764 = true := by
 decide +kernel
def pointBounds21764 : List (Nat × Nat × Nat) := [(2856609792,101114202435620,101114583440237),(2856699904,101114601100355,101114982105188)]
theorem point_links_checked21764 : (cuts21764.take 2).map (fun c => (2856583169-1+2*2^9*c.k,101114081533121+c.lower,101114462537669+c.upper)) = pointBounds21764 := by
 decide +kernel
def cuts21765 : List PrefixCut := [⟨74,341011274,341011468⟩,
⟨128,593537078,593537413⟩]
theorem checked21765 : checkPrefixCuts (2^48) 2856714241 9 Manual.Count131072.C021765.packed 128 cuts21765 = true := by
 decide +kernel
def pointBounds21765 : List (Nat × Nat × Nat) := [(2856790016,101115006649592,101115387654657)]
theorem point_links_checked21765 : (cuts21765.take 1).map (fun c => (2856714241-1+2*2^9*c.k,101114665638318+c.lower,101115046643189+c.upper)) = pointBounds21765 := by
 decide +kernel
def cuts21766 : List PrefixCut := [⟨34,155375294,155375386⟩,
⟨122,563854601,563854932⟩,
⟨128,594494962,594495308⟩]
theorem checked21766 : checkPrefixCuts (2^48) 2856845313 9 Manual.Count131072.C021766.packed 128 cuts21766 = true := by
 decide +kernel
def pointBounds21766 : List (Nat × Nat × Nat) := [(2856880128,101115414550690,101115795555988),(2856970240,101115823029997,101116204035534)]
theorem point_links_checked21766 : (cuts21766.take 2).map (fun c => (2856845313-1+2*2^9*c.k,101115259175396+c.lower,101115640180602+c.upper)) = pointBounds21766 := by
 decide +kernel
def cuts21767 : List PrefixCut := [⟨82,382555151,382555376⟩,
⟨128,597127929,597128276⟩]
theorem checked21767 : checkPrefixCuts (2^48) 2856976385 9 Manual.Count131072.C021767.packed 128 cuts21767 = true := by
 decide +kernel
def pointBounds21767 : List (Nat × Nat × Nat) := [(2857060352,101116236225509,101116617231286)]
theorem point_links_checked21767 : (cuts21767.take 1).map (fun c => (2856976385-1+2*2^9*c.k,101115853670358+c.lower,101116234675910+c.upper)) = pointBounds21767 := by
 decide +kernel
def cuts21768 : List PrefixCut := [⟨42,192994220,192994329⟩,
⟨128,593061326,593061661⟩]
theorem checked21768 : checkPrefixCuts (2^48) 2857107457 9 Manual.Count131072.C021768.packed 128 cuts21768 = true := by
 decide +kernel
def pointBounds21768 : List (Nat × Nat × Nat) := [(2857150464,101116643792507,101117024798515)]
theorem point_links_checked21768 : (cuts21768.take 1).map (fun c => (2857107457-1+2*2^9*c.k,101116450798287+c.lower,101116831804186+c.upper)) = pointBounds21768 := by
 decide +kernel
def cuts21769 : List PrefixCut := [⟨2,7684004,7684009⟩,
⟨90,418476086,418476337⟩,
⟨128,596284976,596285328⟩]
theorem checked21769 : checkPrefixCuts (2^48) 2857238529 9 Manual.Count131072.C021769.packed 128 cuts21769 = true := by
 decide +kernel
def pointBounds21769 : List (Nat × Nat × Nat) := [(2857240576,101117051543617,101117432549856),(2857330688,101117462335699,101117843342184)]
theorem point_links_checked21769 : (cuts21769.take 2).map (fun c => (2857238529-1+2*2^9*c.k,101117043859613+c.lower,101117424865847+c.upper)) = pointBounds21769 := by
 decide +kernel
def cuts21770 : List PrefixCut := [⟨50,233758330,233758472⟩,
⟨128,597341238,597341583⟩]
theorem checked21770 : checkPrefixCuts (2^48) 2857369601 9 Manual.Count131072.C021770.packed 128 cuts21770 = true := by
 decide +kernel
def pointBounds21770 : List (Nat × Nat × Nat) := [(2857420800,101117873902919,101118254909647)]
theorem point_links_checked21770 : (cuts21770.take 1).map (fun c => (2857369601-1+2*2^9*c.k,101117640144589+c.lower,101118021151175+c.upper)) = pointBounds21770 := by
 decide +kernel
def cuts21771 : List PrefixCut := [⟨10,45804223,45804248⟩,
⟨98,455375448,455375710⟩,
⟨128,591896294,591896635⟩]
theorem checked21771 : checkPrefixCuts (2^48) 2857500673 9 Manual.Count131072.C021771.packed 128 cuts21771 = true := by
 decide +kernel
def pointBounds21771 : List (Nat × Nat × Nat) := [(2857510912,101118283290050,101118664297006),(2857601024,101118692861275,101119073868468)]
theorem point_links_checked21771 : (cuts21771.take 2).map (fun c => (2857500673-1+2*2^9*c.k,101118237485827+c.lower,101118618492758+c.upper)) = pointBounds21771 := by
 decide +kernel
def cuts21772 : List PrefixCut := [⟨58,265452999,265453157⟩,
⟨128,591376492,591376834⟩]
theorem checked21772 : checkPrefixCuts (2^48) 2857631745 9 Manual.Count131072.C021772.packed 128 cuts21772 = true := by
 decide +kernel
def pointBounds21772 : List (Nat × Nat × Nat) := [(2857691136,101119094835120,101119475842550)]
theorem point_links_checked21772 : (cuts21772.take 1).map (fun c => (2857631745-1+2*2^9*c.k,101118829382121+c.lower,101119210389393+c.upper)) = pointBounds21772 := by
 decide +kernel
def cuts21773 : List PrefixCut := [⟨18,80371531,80371576⟩,
⟨106,492563291,492563575⟩,
⟨128,595584572,595584911⟩]
theorem checked21773 : checkPrefixCuts (2^48) 2857762817 9 Manual.Count131072.C021773.packed 128 cuts21773 = true := by
 decide +kernel
def pointBounds21773 : List (Nat × Nat × Nat) := [(2857781248,101119501130144,101119882137803),(2857871360,101119913321904,101120294329802)]
theorem point_links_checked21773 : (cuts21773.take 2).map (fun c => (2857762817-1+2*2^9*c.k,101119420758613+c.lower,101119801766227+c.upper)) = pointBounds21773 := by
 decide +kernel
def cuts21774 : List PrefixCut := [⟨66,303839004,303839179⟩,
⟨128,588072169,588072507⟩]
theorem checked21774 : checkPrefixCuts (2^48) 2857893889 9 Manual.Count131072.C021774.packed 128 cuts21774 = true := by
 decide +kernel
def pointBounds21774 : List (Nat × Nat × Nat) := [(2857961472,101120320182189,101120701190317)]
theorem point_links_checked21774 : (cuts21774.take 1).map (fun c => (2857893889-1+2*2^9*c.k,101120016343185+c.lower,101120397351138+c.upper)) = pointBounds21774 := by
 decide +kernel
def cuts21775 : List PrefixCut := [⟨26,120940021,120940093⟩,
⟨114,520683868,520684168⟩,
⟨128,581939385,581939720⟩]
theorem checked21775 : checkPrefixCuts (2^48) 2858024961 9 Manual.Count131072.C021775.packed 128 cuts21775 = true := by
 decide +kernel
def pointBounds21775 : List (Nat × Nat × Nat) := [(2858051584,101120725355375,101121106363738),(2858141696,101121125099222,101121506107813)]
theorem point_links_checked21775 : (cuts21775.take 2).map (fun c => (2858024961-1+2*2^9*c.k,101120604415354+c.lower,101120985423645+c.upper)) = pointBounds21775 := by
 decide +kernel
def cuts21776 : List PrefixCut := [⟨74,344089058,344089252⟩,
⟨128,595601157,595601490⟩]
theorem checked21776 : checkPrefixCuts (2^48) 2858156033 9 Manual.Count131072.C021776.packed 128 cuts21776 = true := by
 decide +kernel
def pointBounds21776 : List (Nat × Nat × Nat) := [(2858231808,101121530443797,101121911452617)]
theorem point_links_checked21776 : (cuts21776.take 1).map (fun c => (2858156033-1+2*2^9*c.k,101121186354739+c.lower,101121567363365+c.upper)) = pointBounds21776 := by
 decide +kernel
def cuts21777 : List PrefixCut := [⟨34,161500930,161501020⟩,
⟨122,566820025,566820345⟩,
⟨128,593702981,593703315⟩]
theorem checked21777 : checkPrefixCuts (2^48) 2858287105 9 Manual.Count131072.C021777.packed 128 cuts21777 = true := by
 decide +kernel
def pointBounds21777 : List (Nat × Nat × Nat) := [(2858321920,101121943456826,101122324465875),(2858412032,101122348775921,101122729785200)]
theorem point_links_checked21777 : (cuts21777.take 2).map (fun c => (2858287105-1+2*2^9*c.k,101121781955896+c.lower,101122162964855+c.upper)) = pointBounds21777 := by
 decide +kernel
def cuts21778 : List PrefixCut := [⟨82,382460623,382460833⟩,
⟨128,596826677,596827012⟩]
theorem checked21778 : checkPrefixCuts (2^48) 2858418177 9 Manual.Count131072.C021778.packed 128 cuts21778 = true := by
 decide +kernel
def pointBounds21778 : List (Nat × Nat × Nat) := [(2858502144,101122758119500,101123139129003)]
theorem point_links_checked21778 : (cuts21778.take 1).map (fun c => (2858418177-1+2*2^9*c.k,101122375658877+c.lower,101122756668170+c.upper)) = pointBounds21778 := by
 decide +kernel
def cuts21779 : List PrefixCut := [⟨42,196146266,196146379⟩,
⟨128,592959213,592959557⟩]
theorem checked21779 : checkPrefixCuts (2^48) 2858549249 9 Manual.Count131072.C021779.packed 128 cuts21779 = true := by
 decide +kernel
def pointBounds21779 : List (Nat × Nat × Nat) := [(2858592256,101123168631820,101123549641561)]
theorem point_links_checked21779 : (cuts21779.take 1).map (fun c => (2858549249-1+2*2^9*c.k,101122972485554+c.lower,101123353495182+c.upper)) = pointBounds21779 := by
 decide +kernel
def cuts21780 : List PrefixCut := [⟨2,9452467,9452472⟩,
⟨90,418855801,418856039⟩,
⟨128,593818119,593818454⟩]
theorem checked21780 : checkPrefixCuts (2^48) 2858680321 9 Manual.Count131072.C021780.packed 128 cuts21780 = true := by
 decide +kernel
def pointBounds21780 : List (Nat × Nat × Nat) := [(2858682368,101123574897234,101123955907211),(2858772480,101123984300568,101124365310778)]
theorem point_links_checked21780 : (cuts21780.take 2).map (fun c => (2858680321-1+2*2^9*c.k,101123565444767+c.lower,101123946454739+c.upper)) = pointBounds21780 := by
 decide +kernel
def cuts21781 : List PrefixCut := [⟨50,230292878,230293005⟩,
⟨128,590738740,590739074⟩]
theorem checked21781 : checkPrefixCuts (2^48) 2858811393 9 Manual.Count131072.C021781.packed 128 cuts21781 = true := by
 decide +kernel
def pointBounds21781 : List (Nat × Nat × Nat) := [(2858862592,101124389555764,101124770566198)]
theorem point_links_checked21781 : (cuts21781.take 1).map (fun c => (2858811393-1+2*2^9*c.k,101124159262886+c.lower,101124540273193+c.upper)) = pointBounds21781 := by
 decide +kernel
def cuts21782 : List PrefixCut := [⟨10,47553297,47553324⟩,
⟨98,452782956,452783220⟩,
⟨128,590908598,590908941⟩]
theorem checked21782 : checkPrefixCuts (2^48) 2858942465 9 Manual.Count131072.C021782.packed 128 cuts21782 = true := by
 decide +kernel
def pointBounds21782 : List (Nat × Nat × Nat) := [(2858952704,101124797554923,101125178565591),(2859042816,101125202784582,101125583795487)]
theorem point_links_checked21782 : (cuts21782.take 2).map (fun c => (2858942465-1+2*2^9*c.k,101124750001626+c.lower,101125131012267+c.upper)) = pointBounds21782 := by
 decide +kernel
def cuts21783 : List PrefixCut := [⟨58,271029158,271029314⟩,
⟨128,584580941,584581283⟩]
theorem checked21783 : checkPrefixCuts (2^48) 2859073537 9 Manual.Count131072.C021783.packed 128 cuts21783 = true := by
 decide +kernel
def pointBounds21783 : List (Nat × Nat × Nat) := [(2859132928,101125611939382,101125992950522)]
theorem point_links_checked21783 : (cuts21783.take 1).map (fun c => (2859073537-1+2*2^9*c.k,101125340910224+c.lower,101125721921208+c.upper)) = pointBounds21783 := by
 decide +kernel
def cuts21784 : List PrefixCut := [⟨18,83185903,83185953⟩,
⟨106,492019654,492019937⟩,
⟨128,591346674,591347015⟩]
theorem checked21784 : checkPrefixCuts (2^48) 2859204609 9 Manual.Count131072.C021784.packed 128 cuts21784 = true := by
 decide +kernel
def pointBounds21784 : List (Nat × Nat × Nat) := [(2859223040,101126008677068,101126389688444),(2859313152,101126417510819,101126798522428)]
theorem point_links_checked21784 : (cuts21784.take 2).map (fun c => (2859204609-1+2*2^9*c.k,101125925491165+c.lower,101126306502491+c.upper)) = pointBounds21784 := by
 decide +kernel
def cuts21785 : List PrefixCut := [⟨66,298763862,298764036⟩,
⟨128,588563127,588563469⟩]
theorem checked21785 : checkPrefixCuts (2^48) 2859335681 9 Manual.Count131072.C021785.packed 128 cuts21785 = true := by
 decide +kernel
def pointBounds21785 : List (Nat × Nat × Nat) := [(2859403264,101126815601701,101127196613542)]
theorem point_links_checked21785 : (cuts21785.take 1).map (fun c => (2859335681-1+2*2^9*c.k,101126516837839+c.lower,101126897849506+c.upper)) = pointBounds21785 := by
 decide +kernel
def cuts21786 : List PrefixCut := [⟨26,119402494,119402565⟩,
⟨114,523768064,523768368⟩,
⟨128,586567605,586567945⟩]
theorem checked21786 : checkPrefixCuts (2^48) 2859466753 9 Manual.Count131072.C021786.packed 128 cuts21786 = true := by
 decide +kernel
def pointBounds21786 : List (Nat × Nat × Nat) := [(2859493376,101127224803460,101127605815540),(2859583488,101127629169030,101128010181343)]
theorem point_links_checked21786 : (cuts21786.take 2).map (fun c => (2859466753-1+2*2^9*c.k,101127105400966+c.lower,101127486412975+c.upper)) = pointBounds21786 := by
 decide +kernel
def cuts21787 : List PrefixCut := [⟨74,348443363,348443554⟩,
⟨128,601994111,601994447⟩]
theorem checked21787 : checkPrefixCuts (2^48) 2859597825 9 Manual.Count131072.C021787.packed 128 cuts21787 = true := by
 decide +kernel
def pointBounds21787 : List (Nat × Nat × Nat) := [(2859673600,101128040411934,101128421424474)]
theorem point_links_checked21787 : (cuts21787.take 1).map (fun c => (2859597825-1+2*2^9*c.k,101127691968571+c.lower,101128072980920+c.upper)) = pointBounds21787 := by
 decide +kernel
def cuts21788 : List PrefixCut := [⟨34,154234368,154234458⟩,
⟨122,560431817,560432143⟩,
⟨128,586907530,586907871⟩]
theorem checked21788 : checkPrefixCuts (2^48) 2859728897 9 Manual.Count131072.C021788.packed 128 cuts21788 = true := by
 decide +kernel
def pointBounds21788 : List (Nat × Nat × Nat) := [(2859763712,101128448197050,101128829209825),(2859853824,101128854394499,101129235407510)]
theorem point_links_checked21788 : (cuts21788.take 2).map (fun c => (2859728897-1+2*2^9*c.k,101128293962682+c.lower,101128674975367+c.upper)) = pointBounds21788 := by
 decide +kernel
def cuts21789 : List PrefixCut := [⟨82,385712593,385712813⟩,
⟨128,596919559,596919901⟩]
theorem checked21789 : checkPrefixCuts (2^48) 2859859969 9 Manual.Count131072.C021789.packed 128 cuts21789 = true := by
 decide +kernel
def pointBounds21789 : List (Nat × Nat × Nat) := [(2859943936,101129266582805,101129647596051)]
theorem point_links_checked21789 : (cuts21789.take 1).map (fun c => (2859859969-1+2*2^9*c.k,101128880870212+c.lower,101129261883238+c.upper)) = pointBounds21789 := by
 decide +kernel
def cuts21790 : List PrefixCut := [⟨42,193980626,193980739⟩,
⟨128,594530183,594530526⟩]
theorem checked21790 : checkPrefixCuts (2^48) 2859991041 9 Manual.Count131072.C021790.packed 128 cuts21790 = true := by
 decide +kernel
def pointBounds21790 : List (Nat × Nat × Nat) := [(2860034048,101129671770397,101130052783878)]
theorem point_links_checked21790 : (cuts21790.take 1).map (fun c => (2859991041-1+2*2^9*c.k,101129477789771+c.lower,101129858803139+c.upper)) = pointBounds21790 := by
 decide +kernel
def cuts21791 : List PrefixCut := [⟨2,8365153,8365157⟩,
⟨90,411558995,411559236⟩,
⟨128,588991790,588992136⟩]
theorem checked21791 : checkPrefixCuts (2^48) 2860122113 9 Manual.Count131072.C021791.packed 128 cuts21791 = true := by
 decide +kernel
def pointBounds21791 : List (Nat × Nat × Nat) := [(2860124160,101130080685107,101130461698822),(2860214272,101130483878949,101130864892901)]
theorem point_links_checked21791 : (cuts21791.take 2).map (fun c => (2860122113-1+2*2^9*c.k,101130072319954+c.lower,101130453333665+c.upper)) = pointBounds21791 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000055
