import PlattAssemblyKernel
import PlattCertificates.Count131072.C019824
import PlattCertificates.Count131072.C019825
import PlattCertificates.Count131072.C019826
import PlattCertificates.Count131072.C019827
import PlattCertificates.Count131072.C019828
import PlattCertificates.Count131072.C019829
import PlattCertificates.Count131072.C019830
import PlattCertificates.Count131072.C019831
import PlattCertificates.Count131072.C019832
import PlattCertificates.Count131072.C019833
import PlattCertificates.Count131072.C019834
import PlattCertificates.Count131072.C019835
import PlattCertificates.Count131072.C019836
import PlattCertificates.Count131072.C019837
import PlattCertificates.Count131072.C019838
import PlattCertificates.Count131072.C019839
import PlattCertificates.Count131072.C019840
import PlattCertificates.Count131072.C019841
import PlattCertificates.Count131072.C019842
import PlattCertificates.Count131072.C019843
import PlattCertificates.Count131072.C019844
import PlattCertificates.Count131072.C019845
import PlattCertificates.Count131072.C019846
import PlattCertificates.Count131072.C019847
import PlattCertificates.Count131072.C019848
import PlattCertificates.Count131072.C019849
import PlattCertificates.Count131072.C019850
import PlattCertificates.Count131072.C019851
import PlattCertificates.Count131072.C019852
import PlattCertificates.Count131072.C019853
import PlattCertificates.Count131072.C019854
import PlattCertificates.Count131072.C019855
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000307
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts19824 : List PrefixCut := [⟨13,69116455,69116494⟩,
⟨93,481860692,481860970⟩,
⟨128,658592564,658592946⟩]
theorem checked19824 : checkPrefixCuts (2^48) 2602303489 9 Manual.Count131072.C019824.packed 128 cuts19824 = true := by
 decide +kernel
def pointBounds19824 : List (Nat × Nat × Nat) := [(2602316800,99906406201955,99906786504353),(2602398720,99906818946192,99907199248829)]
theorem point_links_checked19824 : (cuts19824.take 2).map (fun c => (2602303489-1+2*2^9*c.k,99906337085500+c.lower,99906717387859+c.upper)) = pointBounds19824 := by
 decide +kernel
def cuts19825 : List PrefixCut := [⟨45,233836174,233836306⟩,
⟨125,637145017,637145392⟩,
⟨128,652394578,652394962⟩]
theorem checked19825 : checkPrefixCuts (2^48) 2602434561 9 Manual.Count131072.C019825.packed 128 cuts19825 = true := by
 decide +kernel
def pointBounds19825 : List (Nat × Nat × Nat) := [(2602480640,99907229514238,99907609817111),(2602562560,99907632823081,99908013126197)]
theorem point_links_checked19825 : (cuts19825.take 2).map (fun c => (2602434561-1+2*2^9*c.k,99906995678064+c.lower,99907375980805+c.upper)) = pointBounds19825 := by
 decide +kernel
def cuts19826 : List PrefixCut := [⟨77,395508941,395509171⟩,
⟨128,654416417,654416800⟩]
theorem checked19826 : checkPrefixCuts (2^48) 2602565633 9 Manual.Count131072.C019826.packed 128 cuts19826 = true := by
 decide +kernel
def pointBounds19826 : List (Nat × Nat × Nat) := [(2602644480,99908043581583,99908423884938)]
theorem point_links_checked19826 : (cuts19826.take 1).map (fun c => (2602565633-1+2*2^9*c.k,99907648072642+c.lower,99908028375767+c.upper)) = pointBounds19826 := by
 decide +kernel
def cuts19827 : List PrefixCut := [⟨29,149026287,149026373⟩,
⟨109,557920489,557920818⟩,
⟨128,655681181,655681568⟩]
theorem checked19827 : checkPrefixCuts (2^48) 2602696705 9 Manual.Count131072.C019827.packed 128 cuts19827 = true := by
 decide +kernel
def pointBounds19827 : List (Nat × Nat × Nat) := [(2602726400,99908451515346,99908831818940),(2602808320,99908860409548,99909240713385)]
theorem point_links_checked19827 : (cuts19827.take 2).map (fun c => (2602696705-1+2*2^9*c.k,99908302489059+c.lower,99908682792567+c.upper)) = pointBounds19827 := by
 decide +kernel
def cuts19828 : List PrefixCut := [⟨61,307119445,307119629⟩,
⟨128,642887713,642888092⟩]
theorem checked19828 : checkPrefixCuts (2^48) 2602827777 9 Manual.Count131072.C019828.packed 128 cuts19828 = true := by
 decide +kernel
def pointBounds19828 : List (Nat × Nat × Nat) := [(2602890240,99909265289685,99909645593764)]
theorem point_links_checked19828 : (cuts19828.take 1).map (fun c => (2602827777-1+2*2^9*c.k,99908958170240+c.lower,99909338474135+c.upper)) = pointBounds19828 := by
 decide +kernel
def cuts19829 : List PrefixCut := [⟨13,67585151,67585191⟩,
⟨93,465519188,465519466⟩,
⟨128,642314684,642315067⟩]
theorem checked19829 : checkPrefixCuts (2^48) 2602958849 9 Manual.Count131072.C019829.packed 128 cuts19829 = true := by
 decide +kernel
def pointBounds19829 : List (Nat × Nat × Nat) := [(2602972160,99909668643104,99910048947418),(2603054080,99910066577141,99910446881693)]
theorem point_links_checked19829 : (cuts19829.take 2).map (fun c => (2602958849-1+2*2^9*c.k,99909601057953+c.lower,99909981362227+c.upper)) = pointBounds19829 := by
 decide +kernel
def cuts19830 : List PrefixCut := [⟨45,225775678,225775813⟩,
⟨125,628442335,628442708⟩,
⟨128,646174948,646175331⟩]
theorem checked19830 : checkPrefixCuts (2^48) 2603089921 9 Manual.Count131072.C019830.packed 128 cuts19830 = true := by
 decide +kernel
def pointBounds19830 : List (Nat × Nat × Nat) := [(2603136000,99910469148315,99910849453107),(2603217920,99910871814972,99911252120002)]
theorem point_links_checked19830 : (cuts19830.take 2).map (fun c => (2603089921-1+2*2^9*c.k,99910243372637+c.lower,99910623677294+c.upper)) = pointBounds19830 := by
 decide +kernel
def cuts19831 : List PrefixCut := [⟨77,395625663,395625895⟩,
⟨128,651008078,651008458⟩]
theorem checked19831 : checkPrefixCuts (2^48) 2603220993 9 Manual.Count131072.C019831.packed 128 cuts19831 = true := by
 decide +kernel
def pointBounds19831 : List (Nat × Nat × Nat) := [(2603299840,99911285173248,99911665478520)]
theorem point_links_checked19831 : (cuts19831.take 1).map (fun c => (2603220993-1+2*2^9*c.k,99910889547585+c.lower,99911269852625+c.upper)) = pointBounds19831 := by
 decide +kernel
def cuts19832 : List PrefixCut := [⟨29,150718660,150718750⟩,
⟨109,557671961,557672295⟩,
⟨128,652164593,652164983⟩]
theorem checked19832 : checkPrefixCuts (2^48) 2603352065 9 Manual.Count131072.C019832.packed 128 cuts19832 = true := by
 decide +kernel
def pointBounds19832 : List (Nat × Nat × Nat) := [(2603381760,99911691274323,99912071579833),(2603463680,99912098227624,99912478533378)]
theorem point_links_checked19832 : (cuts19832.take 2).map (fun c => (2603352065-1+2*2^9*c.k,99911540555663+c.lower,99911920861083+c.upper)) = pointBounds19832 := by
 decide +kernel
def cuts19833 : List PrefixCut := [⟨61,316664293,316664480⟩,
⟨128,661321222,661321613⟩]
theorem checked19833 : checkPrefixCuts (2^48) 2603483137 9 Manual.Count131072.C019833.packed 128 cuts19833 = true := by
 decide +kernel
def pointBounds19833 : List (Nat × Nat × Nat) := [(2603545600,99912509384549,99912889690546)]
theorem point_links_checked19833 : (cuts19833.take 1).map (fun c => (2603483137-1+2*2^9*c.k,99912192720256+c.lower,99912573026066+c.upper)) = pointBounds19833 := by
 decide +kernel
def cuts19834 : List PrefixCut := [⟨13,67568138,67568177⟩,
⟨93,479347911,479348191⟩,
⟨128,656098910,656099297⟩]
theorem checked19834 : checkPrefixCuts (2^48) 2603614209 9 Manual.Count131072.C019834.packed 128 cuts19834 = true := by
 decide +kernel
def pointBounds19834 : List (Nat × Nat × Nat) := [(2603627520,99912921609616,99913301915856),(2603709440,99913333389389,99913713695870)]
theorem point_links_checked19834 : (cuts19834.take 2).map (fun c => (2603614209-1+2*2^9*c.k,99912854041478+c.lower,99913234347679+c.upper)) = pointBounds19834 := by
 decide +kernel
def cuts19835 : List PrefixCut := [⟨45,228745702,228745836⟩,
⟨125,640499502,640499879⟩,
⟨128,655849485,655849871⟩]
theorem checked19835 : checkPrefixCuts (2^48) 2603745281 9 Manual.Count131072.C019835.packed 128 cuts19835 = true := by
 decide +kernel
def pointBounds19835 : List (Nat × Nat × Nat) := [(2603791360,99913738886090,99914119192812),(2603873280,99914150639890,99914530946855)]
theorem point_links_checked19835 : (cuts19835.take 2).map (fun c => (2603745281-1+2*2^9*c.k,99913510140388+c.lower,99913890446976+c.upper)) = pointBounds19835 := by
 decide +kernel
def cuts19836 : List PrefixCut := [⟨77,393256011,393256249⟩,
⟨128,657221675,657222069⟩]
theorem checked19836 : checkPrefixCuts (2^48) 2603876353 9 Manual.Count131072.C019836.packed 128 cuts19836 = true := by
 decide +kernel
def pointBounds19836 : List (Nat × Nat × Nat) := [(2603955200,99914559245884,99914939553096)]
theorem point_links_checked19836 : (cuts19836.take 1).map (fun c => (2603876353-1+2*2^9*c.k,99914165989873+c.lower,99914546296847+c.upper)) = pointBounds19836 := by
 decide +kernel
def cuts19837 : List PrefixCut := [⟨29,147005597,147005685⟩,
⟨109,562287532,562287861⟩,
⟨128,657621091,657621477⟩]
theorem checked19837 : checkPrefixCuts (2^48) 2604007425 9 Manual.Count131072.C019837.packed 128 cuts19837 = true := by
 decide +kernel
def pointBounds19837 : List (Nat × Nat × Nat) := [(2604037120,99914970217145,99915350524601),(2604119040,99915385499080,99915765806777)]
theorem point_links_checked19837 : (cuts19837.take 2).map (fun c => (2604007425-1+2*2^9*c.k,99914823211548+c.lower,99915203518916+c.upper)) = pointBounds19837 := by
 decide +kernel
def cuts19838 : List PrefixCut := [⟨61,308586180,308586360⟩,
⟨128,653264482,653264868⟩]
theorem checked19838 : checkPrefixCuts (2^48) 2604138497 9 Manual.Count131072.C019838.packed 128 cuts19838 = true := by
 decide +kernel
def pointBounds19838 : List (Nat × Nat × Nat) := [(2604200960,99915789418819,99916169726753)]
theorem point_links_checked19838 : (cuts19838.take 1).map (fun c => (2604138497-1+2*2^9*c.k,99915480832639+c.lower,99915861140393+c.upper)) = pointBounds19838 := by
 decide +kernel
def cuts19839 : List PrefixCut := [⟨13,64308679,64308717⟩,
⟨93,471229392,471229674⟩,
⟨128,656582127,656582515⟩]
theorem checked19839 : checkPrefixCuts (2^48) 2604269569 9 Manual.Count131072.C019839.packed 128 cuts19839 = true := by
 decide +kernel
def pointBounds19839 : List (Nat × Nat × Nat) := [(2604282880,99916198405800,99916578713978),(2604364800,99916605326513,99916985634935)]
theorem point_links_checked19839 : (cuts19839.take 2).map (fun c => (2604269569-1+2*2^9*c.k,99916134097121+c.lower,99916514405261+c.upper)) = pointBounds19839 := by
 decide +kernel
def cuts19840 : List PrefixCut := [⟨45,235280820,235280960⟩,
⟨125,642499981,642500357⟩,
⟨128,658494530,658494915⟩]
theorem checked19840 : checkPrefixCuts (2^48) 2604400641 9 Manual.Count131072.C019840.packed 128 cuts19840 = true := by
 decide +kernel
def pointBounds19840 : List (Nat × Nat × Nat) := [(2604446720,99917025960068,99917406268736),(2604528640,99917433179229,99917813488133)]
theorem point_links_checked19840 : (cuts19840.take 2).map (fun c => (2604400641-1+2*2^9*c.k,99916790679248+c.lower,99917170987776+c.upper)) = pointBounds19840 := by
 decide +kernel
def cuts19841 : List PrefixCut := [⟨77,393913500,393913730⟩,
⟨128,653165870,653166254⟩]
theorem checked19841 : checkPrefixCuts (2^48) 2604531713 9 Manual.Count131072.C019841.packed 128 cuts19841 = true := by
 decide +kernel
def pointBounds19841 : List (Nat × Nat × Nat) := [(2604610560,99917843087278,99918223396421)]
theorem point_links_checked19841 : (cuts19841.take 1).map (fun c => (2604531713-1+2*2^9*c.k,99917449173778+c.lower,99917829482691+c.upper)) = pointBounds19841 := by
 decide +kernel
def cuts19842 : List PrefixCut := [⟨29,154100933,154101023⟩,
⟨109,562578405,562578735⟩,
⟨128,657996045,657996432⟩]
theorem checked19842 : checkPrefixCuts (2^48) 2604662785 9 Manual.Count131072.C019842.packed 128 cuts19842 = true := by
 decide +kernel
def pointBounds19842 : List (Nat × Nat × Nat) := [(2604692480,99918256440581,99918636749968),(2604774400,99918664918053,99919045227680)]
theorem point_links_checked19842 : (cuts19842.take 2).map (fun c => (2604662785-1+2*2^9*c.k,99918102339648+c.lower,99918482648945+c.upper)) = pointBounds19842 := by
 decide +kernel
def cuts19843 : List PrefixCut := [⟨61,312182542,312182723⟩,
⟨128,653856599,653856985⟩]
theorem checked19843 : checkPrefixCuts (2^48) 2604793857 9 Manual.Count131072.C019843.packed 128 cuts19843 = true := by
 decide +kernel
def pointBounds19843 : List (Nat × Nat × Nat) := [(2604856320,99919072518235,99919452828100)]
theorem point_links_checked19843 : (cuts19843.take 1).map (fun c => (2604793857-1+2*2^9*c.k,99918760335693+c.lower,99919140645377+c.upper)) = pointBounds19843 := by
 decide +kernel
def cuts19844 : List PrefixCut := [⟨13,63211949,63211987⟩,
⟨93,470354255,470354524⟩,
⟨128,647988796,647989171⟩]
theorem checked19844 : checkPrefixCuts (2^48) 2604924929 9 Manual.Count131072.C019844.packed 128 cuts19844 = true := by
 decide +kernel
def pointBounds19844 : List (Nat × Nat × Nat) := [(2604938240,99919477404241,99919857714349),(2605020160,99919884546547,99920264856886)]
theorem point_links_checked19844 : (cuts19844.take 2).map (fun c => (2604924929-1+2*2^9*c.k,99919414192292+c.lower,99919794502362+c.upper)) = pointBounds19844 := by
 decide +kernel
def cuts19845 : List PrefixCut := [⟨45,233168673,233168810⟩,
⟨125,645687657,645688038⟩,
⟨128,660273609,660274000⟩]
theorem checked19845 : checkPrefixCuts (2^48) 2605056001 9 Manual.Count131072.C019845.packed 128 cuts19845 = true := by
 decide +kernel
def pointBounds19845 : List (Nat × Nat × Nat) := [(2605102080,99920295349761,99920675660343),(2605184000,99920707868745,99921088179571)]
theorem point_links_checked19845 : (cuts19845.take 2).map (fun c => (2605056001-1+2*2^9*c.k,99920062181088+c.lower,99920442491533+c.upper)) = pointBounds19845 := by
 decide +kernel
def cuts19846 : List PrefixCut := [⟨77,387007815,387008044⟩,
⟨128,645114587,645114969⟩]
theorem checked19846 : checkPrefixCuts (2^48) 2605187073 9 Manual.Count131072.C019846.packed 128 cuts19846 = true := by
 decide +kernel
def pointBounds19846 : List (Nat × Nat × Nat) := [(2605265920,99921109462512,99921489773577)]
theorem point_links_checked19846 : (cuts19846.take 1).map (fun c => (2605187073-1+2*2^9*c.k,99920722454697+c.lower,99921102765533+c.upper)) = pointBounds19846 := by
 decide +kernel
def cuts19847 : List PrefixCut := [⟨29,150388859,150388950⟩,
⟨109,558439533,558439862⟩,
⟨128,653509067,653509449⟩]
theorem checked19847 : checkPrefixCuts (2^48) 2605318145 9 Manual.Count131072.C019847.packed 128 cuts19847 = true := by
 decide +kernel
def pointBounds19847 : List (Nat × Nat × Nat) := [(2605347840,99921517958143,99921898269452),(2605429760,99921926008817,99922306320364)]
theorem point_links_checked19847 : (cuts19847.take 2).map (fun c => (2605318145-1+2*2^9*c.k,99921367569284+c.lower,99921747880502+c.upper)) = pointBounds19847 := by
 decide +kernel
def cuts19848 : List PrefixCut := [⟨61,308538935,308539122⟩,
⟨128,642673019,642673398⟩]
theorem checked19848 : checkPrefixCuts (2^48) 2605449217 9 Manual.Count131072.C019848.packed 128 cuts19848 = true := by
 decide +kernel
def pointBounds19848 : List (Nat × Nat × Nat) := [(2605511680,99922329617286,99922709929073)]
theorem point_links_checked19848 : (cuts19848.take 1).map (fun c => (2605449217-1+2*2^9*c.k,99922021078351+c.lower,99922401389951+c.upper)) = pointBounds19848 := by
 decide +kernel
def cuts19849 : List PrefixCut := [⟨13,64492382,64492421⟩,
⟨93,476069386,476069664⟩,
⟨128,654199349,654199734⟩]
theorem checked19849 : checkPrefixCuts (2^48) 2605580289 9 Manual.Count131072.C019849.packed 128 cuts19849 = true := by
 decide +kernel
def pointBounds19849 : List (Nat × Nat × Nat) := [(2605593600,99922728243752,99923108555770),(2605675520,99923139820756,99923520133013)]
theorem point_links_checked19849 : (cuts19849.take 2).map (fun c => (2605580289-1+2*2^9*c.k,99922663751370+c.lower,99923044063349+c.upper)) = pointBounds19849 := by
 decide +kernel
def cuts19850 : List PrefixCut := [⟨45,224252252,224252386⟩,
⟨125,636667532,636667907⟩,
⟨128,651681883,651682267⟩]
theorem checked19850 : checkPrefixCuts (2^48) 2605711361 9 Manual.Count131072.C019850.packed 128 cuts19850 = true := by
 decide +kernel
def pointBounds19850 : List (Nat × Nat × Nat) := [(2605757440,99923542202971,99923922515469),(2605839360,99923954618251,99924334930990)]
theorem point_links_checked19850 : (cuts19850.take 2).map (fun c => (2605711361-1+2*2^9*c.k,99923317950719+c.lower,99923698263083+c.upper)) = pointBounds19850 := by
 decide +kernel
def cuts19851 : List PrefixCut := [⟨77,393175408,393175644⟩,
⟨128,656833917,656834303⟩]
theorem checked19851 : checkPrefixCuts (2^48) 2605842433 9 Manual.Count131072.C019851.packed 128 cuts19851 = true := by
 decide +kernel
def pointBounds19851 : List (Nat × Nat × Nat) := [(2605921280,99924362808010,99924743120994)]
theorem point_links_checked19851 : (cuts19851.take 1).map (fun c => (2605842433-1+2*2^9*c.k,99923969632602+c.lower,99924349945350+c.upper)) = pointBounds19851 := by
 decide +kernel
def cuts19852 : List PrefixCut := [⟨29,144518474,144518561⟩,
⟨109,555598844,555599166⟩,
⟨128,652480571,652480951⟩]
theorem checked19852 : checkPrefixCuts (2^48) 2605973505 9 Manual.Count131072.C019852.packed 128 cuts19852 = true := by
 decide +kernel
def pointBounds19852 : List (Nat × Nat × Nat) := [(2606003200,99924770984993,99925151298214),(2606085120,99925182065363,99925562378819)]
theorem point_links_checked19852 : (cuts19852.take 2).map (fun c => (2605973505-1+2*2^9*c.k,99924626466519+c.lower,99925006779653+c.upper)) = pointBounds19852 := by
 decide +kernel
def cuts19853 : List PrefixCut := [⟨61,316129710,316129896⟩,
⟨128,655039972,655040360⟩]
theorem checked19853 : checkPrefixCuts (2^48) 2606104577 9 Manual.Count131072.C019853.packed 128 cuts19853 = true := by
 decide +kernel
def pointBounds19853 : List (Nat × Nat × Nat) := [(2606167040,99925595076800,99925975390500)]
theorem point_links_checked19853 : (cuts19853.take 1).map (fun c => (2606104577-1+2*2^9*c.k,99925278947090+c.lower,99925659260604+c.upper)) = pointBounds19853 := by
 decide +kernel
def cuts19854 : List PrefixCut := [⟨13,65340169,65340207⟩,
⟨93,471305806,471306083⟩,
⟨128,650902943,650903326⟩]
theorem checked19854 : checkPrefixCuts (2^48) 2606235649 9 Manual.Count131072.C019854.packed 128 cuts19854 = true := by
 decide +kernel
def pointBounds19854 : List (Nat × Nat × Nat) := [(2606248960,99925999327231,99926379641171),(2606330880,99926405292868,99926785607047)]
theorem point_links_checked19854 : (cuts19854.take 2).map (fun c => (2606235649-1+2*2^9*c.k,99925933987062+c.lower,99926314300964+c.upper)) = pointBounds19854 := by
 decide +kernel
def cuts19855 : List PrefixCut := [⟨45,233159405,233159545⟩,
⟨125,639639490,639639872⟩,
⟨128,654110117,654110508⟩]
theorem checked19855 : checkPrefixCuts (2^48) 2606366721 9 Manual.Count131072.C019855.packed 128 cuts19855 = true := by
 decide +kernel
def pointBounds19855 : List (Nat × Nat × Nat) := [(2606412800,99926818049410,99927198363835),(2606494720,99927224529495,99927604844162)]
theorem point_links_checked19855 : (cuts19855.take 2).map (fun c => (2606366721-1+2*2^9*c.k,99926584890005+c.lower,99926965204290+c.upper)) = pointBounds19855 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000307
