import PlattAssemblyKernel
import PlattCertificates.Count131072.C011824
import PlattCertificates.Count131072.C011825
import PlattCertificates.Count131072.C011826
import PlattCertificates.Count131072.C011827
import PlattCertificates.Count131072.C011828
import PlattCertificates.Count131072.C011829
import PlattCertificates.Count131072.C011830
import PlattCertificates.Count131072.C011831
import PlattCertificates.Count131072.C011832
import PlattCertificates.Count131072.C011833
import PlattCertificates.Count131072.C011834
import PlattCertificates.Count131072.C011835
import PlattCertificates.Count131072.C011836
import PlattCertificates.Count131072.C011837
import PlattCertificates.Count131072.C011838
import PlattCertificates.Count131072.C011839
import PlattCertificates.Count131072.C011840
import PlattCertificates.Count131072.C011841
import PlattCertificates.Count131072.C011842
import PlattCertificates.Count131072.C011843
import PlattCertificates.Count131072.C011844
import PlattCertificates.Count131072.C011845
import PlattCertificates.Count131072.C011846
import PlattCertificates.Count131072.C011847
import PlattCertificates.Count131072.C011848
import PlattCertificates.Count131072.C011849
import PlattCertificates.Count131072.C011850
import PlattCertificates.Count131072.C011851
import PlattCertificates.Count131072.C011852
import PlattCertificates.Count131072.C011853
import PlattCertificates.Count131072.C011854
import PlattCertificates.Count131072.C011855
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000057
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts11824 : List PrefixCut := [⟨9,79529457,79529520⟩,
⟨57,499632794,499633176⟩,
⟨105,918998271,918998977⟩,
⟨128,1121339582,1121340443⟩]
theorem checked11824 : checkPrefixCuts (2^48) 1553727489 9 Manual.Count131072.C011824.packed 128 cuts11824 = true := by
 decide +kernel
def pointBounds11824 : List (Nat × Nat × Nat) := [(1553736704,93129511664875,93129887450145),(1553785856,93129931768212,93130307553801),(1553835008,93130351133689,93130726919602)]
theorem point_links_checked11824 : (cuts11824.take 3).map (fun c => (1553727489-1+2*2^9*c.k,93129432135418+c.lower,93129807920625+c.upper)) = pointBounds11824 := by
 decide +kernel
def cuts11825 : List PrefixCut := [⟨25,222807446,222807621⟩,
⟨73,641240559,641241061⟩,
⟨121,1069804038,1069804872⟩,
⟨128,1131026274,1131027157⟩]
theorem checked11825 : checkPrefixCuts (2^48) 1553858561 9 Manual.Count131072.C011825.packed 128 cuts11825 = true := by
 decide +kernel
def pointBounds11825 : List (Nat × Nat × Nat) := [(1553884160,93130776282446,93131152068689),(1553933312,93131194715559,93131570502129),(1553982464,93131623279038,93131999065940)]
theorem point_links_checked11825 : (cuts11825.take 3).map (fun c => (1553858561-1+2*2^9*c.k,93130553475000+c.lower,93130929261068+c.upper)) = pointBounds11825 := by
 decide +kernel
def cuts11826 : List PrefixCut := [⟨41,357909007,357909285⟩,
⟨89,783547461,783548071⟩,
⟨128,1118614918,1118615790⟩]
theorem checked11826 : checkPrefixCuts (2^48) 1553989633 9 Manual.Count131072.C011826.packed 128 cuts11826 = true := by
 decide +kernel
def pointBounds11826 : List (Nat × Nat × Nat) := [(1554031616,93132042410281,93132418197510),(1554080768,93132468048735,93132843836296)]
theorem point_links_checked11826 : (cuts11826.take 2).map (fun c => (1553989633-1+2*2^9*c.k,93131684501274+c.lower,93132060288225+c.upper)) = pointBounds11826 := by
 decide +kernel
def cuts11827 : List PrefixCut := [⟨9,78060414,78060474⟩,
⟨57,505845117,505845505⟩,
⟨105,923836693,923837404⟩,
⟨128,1128662262,1128663131⟩]
theorem checked11827 : checkPrefixCuts (2^48) 1554120705 9 Manual.Count131072.C011827.packed 128 cuts11827 = true := by
 decide +kernel
def pointBounds11827 : List (Nat × Nat × Nat) := [(1554129920,93132881176606,93133256964489),(1554179072,93133308961309,93133684749520),(1554228224,93133726952885,93134102741419)]
theorem point_links_checked11827 : (cuts11827.take 3).map (fun c => (1554120705-1+2*2^9*c.k,93132803116192+c.lower,93133178904015+c.upper)) = pointBounds11827 := by
 decide +kernel
def cuts11828 : List PrefixCut := [⟨25,215688212,215688380⟩,
⟨73,630755761,630756249⟩,
⟨121,1047258915,1047259721⟩,
⟨128,1110819772,1110820626⟩]
theorem checked11828 : checkPrefixCuts (2^48) 1554251777 9 Manual.Count131072.C011828.packed 128 cuts11828 = true := by
 decide +kernel
def pointBounds11828 : List (Nat × Nat × Nat) := [(1554277376,93134147466666,93134523255526),(1554326528,93134562534215,93134938323395),(1554375680,93134979037369,93135354826867)]
theorem point_links_checked11828 : (cuts11828.take 3).map (fun c => (1554251777-1+2*2^9*c.k,93133931778454+c.lower,93134307567146+c.upper)) = pointBounds11828 := by
 decide +kernel
def cuts11829 : List PrefixCut := [⟨41,360715689,360715968⟩,
⟨89,783892370,783892977⟩,
⟨128,1129377165,1129378037⟩]
theorem checked11829 : checkPrefixCuts (2^48) 1554382849 9 Manual.Count131072.C011829.packed 128 cuts11829 = true := by
 decide +kernel
def pointBounds11829 : List (Nat × Nat × Nat) := [(1554424832,93135403313915,93135779103740),(1554473984,93135826490596,93136202280749)]
theorem point_links_checked11829 : (cuts11829.take 2).map (fun c => (1554382849-1+2*2^9*c.k,93135042598226+c.lower,93135418387772+c.upper)) = pointBounds11829 := by
 decide +kernel
def cuts11830 : List PrefixCut := [⟨9,78583883,78583945⟩,
⟨57,501371703,501372096⟩,
⟨105,915093172,915093885⟩,
⟨128,1114616329,1114617197⟩]
theorem checked11830 : checkPrefixCuts (2^48) 1554513921 9 Manual.Count131072.C011830.packed 128 cuts11830 = true := by
 decide +kernel
def pointBounds11830 : List (Nat × Nat × Nat) := [(1554523136,93136250559274,93136626349754),(1554572288,93136673347094,93137049137905),(1554621440,93137087068563,93137462859694)]
theorem point_links_checked11830 : (cuts11830.take 3).map (fun c => (1554513921-1+2*2^9*c.k,93136171975391+c.lower,93136547765809+c.upper)) = pointBounds11830 := by
 decide +kernel
def cuts11831 : List PrefixCut := [⟨25,212012611,212012777⟩,
⟨73,630053139,630053627⟩,
⟨121,1060029215,1060030040⟩,
⟨128,1123030880,1123031752⟩]
theorem checked11831 : checkPrefixCuts (2^48) 1554644993 9 Manual.Count131072.C011831.packed 128 cuts11831 = true := by
 decide +kernel
def pointBounds11831 : List (Nat × Nat × Nat) := [(1554670592,93137498604331,93137874395783),(1554719744,93137916644859,93138292436633),(1554768896,93138346620935,93138722413046)]
theorem point_links_checked11831 : (cuts11831.take 3).map (fun c => (1554644993-1+2*2^9*c.k,93137286591720+c.lower,93137662383006+c.upper)) = pointBounds11831 := by
 decide +kernel
def cuts11832 : List PrefixCut := [⟨41,351572739,351573008⟩,
⟨89,772288931,772289529⟩,
⟨128,1121125899,1121126765⟩]
theorem checked11832 : checkPrefixCuts (2^48) 1554776065 9 Manual.Count131072.C011832.packed 128 cuts11832 = true := by
 decide +kernel
def pointBounds11832 : List (Nat × Nat × Nat) := [(1554818048,93138761195339,93139136987766),(1554867200,93139181911531,93139557704287)]
theorem point_links_checked11832 : (cuts11832.take 2).map (fun c => (1554776065-1+2*2^9*c.k,93138409622600+c.lower,93138785414758+c.upper)) = pointBounds11832 := by
 decide +kernel
def cuts11833 : List PrefixCut := [⟨9,80555254,80555315⟩,
⟨57,509209651,509210044⟩,
⟨105,925179492,925180211⟩,
⟨128,1126462297,1126463170⟩]
theorem checked11833 : checkPrefixCuts (2^48) 1554907137 9 Manual.Count131072.C011833.packed 128 cuts11833 = true := by
 decide +kernel
def pointBounds11833 : List (Nat × Nat × Nat) := [(1554916352,93139611303753,93139987096838),(1554965504,93140039958150,93140415751567),(1555014656,93140455927991,93140831721734)]
theorem point_links_checked11833 : (cuts11833.take 3).map (fun c => (1554907137-1+2*2^9*c.k,93139530748499+c.lower,93139906541523+c.upper)) = pointBounds11833 := by
 decide +kernel
def cuts11834 : List PrefixCut := [⟨25,213045061,213045225⟩,
⟨73,634418893,634419379⟩,
⟨121,1053245437,1053246245⟩,
⟨128,1120032040,1120032898⟩]
theorem checked11834 : checkPrefixCuts (2^48) 1555038209 9 Manual.Count131072.C011834.packed 128 cuts11834 = true := by
 decide +kernel
def pointBounds11834 : List (Nat × Nat × Nat) := [(1555063808,93140870255857,93141246049918),(1555112960,93141291629689,93141667424072),(1555162112,93141710456233,93142086250938)]
theorem point_links_checked11834 : (cuts11834.take 3).map (fun c => (1555038209-1+2*2^9*c.k,93140657210796+c.lower,93141033004693+c.upper)) = pointBounds11834 := by
 decide +kernel
def cuts11835 : List PrefixCut := [⟨41,351302734,351303005⟩,
⟨89,771369637,771370230⟩,
⟨128,1113603135,1113603992⟩]
theorem checked11835 : checkPrefixCuts (2^48) 1555169281 9 Manual.Count131072.C011835.packed 128 cuts11835 = true := by
 decide +kernel
def pointBounds11835 : List (Nat × Nat × Nat) := [(1555211264,93142128545570,93142504340596),(1555260416,93142548612473,93142924407821)]
theorem point_links_checked11835 : (cuts11835.take 2).map (fun c => (1555169281-1+2*2^9*c.k,93141777242836+c.lower,93142153037591+c.upper)) = pointBounds11835 := by
 decide +kernel
def cuts11836 : List PrefixCut := [⟨9,76915351,76915410⟩,
⟨57,500575152,500575540⟩,
⟨105,933451062,933451779⟩,
⟨128,1132873310,1132874179⟩]
theorem checked11836 : checkPrefixCuts (2^48) 1555300353 9 Manual.Count131072.C011836.packed 128 cuts11836 = true := by
 decide +kernel
def pointBounds11836 : List (Nat × Nat × Nat) := [(1555309568,93142967761322,93143343556993),(1555358720,93143391421123,93143767217123),(1555407872,93143824297033,93144200093362)]
theorem point_links_checked11836 : (cuts11836.take 3).map (fun c => (1555300353-1+2*2^9*c.k,93142890845971+c.lower,93143266641583+c.upper)) = pointBounds11836 := by
 decide +kernel
def cuts11837 : List PrefixCut := [⟨25,213896015,213896181⟩,
⟨73,630639418,630639908⟩,
⟨121,1053702852,1053703668⟩,
⟨128,1111968027,1111968888⟩]
theorem checked11837 : checkPrefixCuts (2^48) 1555431425 9 Manual.Count131072.C011837.packed 128 cuts11837 = true := by
 decide +kernel
def pointBounds11837 : List (Nat × Nat × Nat) := [(1555457024,93144237615296,93144613411943),(1555506176,93144654358699,93145030155670),(1555555328,93145077422133,93145453219430)]
theorem point_links_checked11837 : (cuts11837.take 3).map (fun c => (1555431425-1+2*2^9*c.k,93144023719281+c.lower,93144399515762+c.upper)) = pointBounds11837 := by
 decide +kernel
def cuts11838 : List PrefixCut := [⟨41,358994622,358994905⟩,
⟨89,788545257,788545869⟩,
⟨128,1133406275,1133407154⟩]
theorem checked11838 : checkPrefixCuts (2^48) 1555562497 9 Manual.Count131072.C011838.packed 128 cuts11838 = true := by
 decide +kernel
def pointBounds11838 : List (Nat × Nat × Nat) := [(1555604480,93145494681930,93145870479555),(1555653632,93145924232565,93146300030519)]
theorem point_links_checked11838 : (cuts11838.take 2).map (fun c => (1555562497-1+2*2^9*c.k,93145135687308+c.lower,93145511484650+c.upper)) = pointBounds11838 := by
 decide +kernel
def cuts11839 : List PrefixCut := [⟨9,76534049,76534108⟩,
⟨57,495201847,495202231⟩,
⟨105,906619466,906620168⟩,
⟨128,1104905809,1104906666⟩]
theorem checked11839 : checkPrefixCuts (2^48) 1555693569 9 Manual.Count131072.C011839.packed 128 cuts11839 = true := by
 decide +kernel
def pointBounds11839 : List (Nat × Nat × Nat) := [(1555702784,93146345627632,93146721425912),(1555751936,93146764295430,93147140094035),(1555801088,93147175713049,93147551511972)]
theorem point_links_checked11839 : (cuts11839.take 3).map (fun c => (1555693569-1+2*2^9*c.k,93146269093583+c.lower,93146644891804+c.upper)) = pointBounds11839 := by
 decide +kernel
def cuts11840 : List PrefixCut := [⟨25,213841934,213842101⟩,
⟨73,637354604,637355099⟩,
⟨121,1050361433,1050362248⟩,
⟨128,1111687219,1111688081⟩]
theorem checked11840 : checkPrefixCuts (2^48) 1555824641 9 Manual.Count131072.C011840.packed 128 cuts11840 = true := by
 decide +kernel
def pointBounds11840 : List (Nat × Nat × Nat) := [(1555850240,93147587841326,93147963640571),(1555899392,93148011353996,93148387153569),(1555948544,93148424360825,93148800160718)]
theorem point_links_checked11840 : (cuts11840.take 3).map (fun c => (1555824641-1+2*2^9*c.k,93147373999392+c.lower,93147749798470+c.upper)) = pointBounds11840 := by
 decide +kernel
def cuts11841 : List PrefixCut := [⟨41,354019661,354019936⟩,
⟨89,782557187,782557793⟩,
⟨128,1117382072,1117382937⟩]
theorem checked11841 : checkPrefixCuts (2^48) 1555955713 9 Manual.Count131072.C011841.packed 128 cuts11841 = true := by
 decide +kernel
def pointBounds11841 : List (Nat × Nat × Nat) := [(1555997696,93148839706272,93149215506487),(1556046848,93149268243798,93149644044344)]
theorem point_links_checked11841 : (cuts11841.take 2).map (fun c => (1555955713-1+2*2^9*c.k,93148485686611+c.lower,93148861486551+c.upper)) = pointBounds11841 := by
 decide +kernel
def cuts11842 : List PrefixCut := [⟨9,79227992,79228052⟩,
⟨57,499598810,499599191⟩,
⟨105,926286983,926287693⟩,
⟨128,1128140674,1128141544⟩]
theorem checked11842 : checkPrefixCuts (2^48) 1556086785 9 Manual.Count131072.C011842.packed 128 cuts11842 = true := by
 decide +kernel
def pointBounds11842 : List (Nat × Nat × Nat) := [(1556096000,93149682296675,93150058097540),(1556145152,93150102667493,93150478468679),(1556194304,93150529355666,93150905157181)]
theorem point_links_checked11842 : (cuts11842.take 3).map (fun c => (1556086785-1+2*2^9*c.k,93149603068683+c.lower,93149978869488+c.upper)) = pointBounds11842 := by
 decide +kernel
def cuts11843 : List PrefixCut := [⟨25,220480115,220480288⟩,
⟨73,630139980,630140474⟩,
⟨121,1048106492,1048107307⟩,
⟨128,1108150781,1108151644⟩]
theorem checked11843 : checkPrefixCuts (2^48) 1556217857 9 Manual.Count131072.C011843.packed 128 cuts11843 = true := by
 decide +kernel
def pointBounds11843 : List (Nat × Nat × Nat) := [(1556243456,93150951689472,93151327491320),(1556292608,93151361349337,93151737151506),(1556341760,93151779315849,93152155118339)]
theorem point_links_checked11843 : (cuts11843.take 3).map (fun c => (1556217857-1+2*2^9*c.k,93150731209357+c.lower,93151107011032+c.upper)) = pointBounds11843 := by
 decide +kernel
def cuts11844 : List PrefixCut := [⟨41,366589984,366590261⟩,
⟨89,783083198,783083797⟩,
⟨128,1121802033,1121802893⟩]
theorem checked11844 : checkPrefixCuts (2^48) 1556348929 9 Manual.Count131072.C011844.packed 128 cuts11844 = true := by
 decide +kernel
def pointBounds11844 : List (Nat × Nat × Nat) := [(1556390912,93152205950122,93152581752937),(1556440064,93152622443336,93152998246473)]
theorem point_links_checked11844 : (cuts11844.take 2).map (fun c => (1556348929-1+2*2^9*c.k,93151839360138+c.lower,93152215162676+c.upper)) = pointBounds11844 := by
 decide +kernel
def cuts11845 : List PrefixCut := [⟨9,79207967,79208029⟩,
⟨57,503812618,503813010⟩,
⟨105,920628156,920628869⟩,
⟨128,1120622588,1120623454⟩]
theorem checked11845 : checkPrefixCuts (2^48) 1556480001 9 Manual.Count131072.C011845.packed 128 cuts11845 = true := by
 decide +kernel
def pointBounds11845 : List (Nat × Nat × Nat) := [(1556489216,93153040370138,93153416173598),(1556538368,93153464974789,93153840778579),(1556587520,93153881790327,93154257594438)]
theorem point_links_checked11845 : (cuts11845.take 3).map (fun c => (1556480001-1+2*2^9*c.k,93152961162171+c.lower,93153336965569+c.upper)) = pointBounds11845 := by
 decide +kernel
def cuts11846 : List PrefixCut := [⟨25,228923132,228923308⟩,
⟨73,647520609,647521107⟩,
⟨121,1077496024,1077496849⟩,
⟨128,1139875690,1139876562⟩]
theorem checked11846 : checkPrefixCuts (2^48) 1556611073 9 Manual.Count131072.C011846.packed 128 cuts11846 = true := by
 decide +kernel
def pointBounds11846 : List (Nat × Nat × Nat) := [(1556636672,93154310707891,93154686512331),(1556685824,93154729305368,93155105110130),(1556734976,93155159280783,93155535085872)]
theorem point_links_checked11846 : (cuts11846.take 3).map (fun c => (1556611073-1+2*2^9*c.k,93154081784759+c.lower,93154457589023+c.upper)) = pointBounds11846 := by
 decide +kernel
def cuts11847 : List PrefixCut := [⟨41,361253910,361254182⟩,
⟨89,788851758,788852359⟩,
⟨128,1122241967,1122242824⟩]
theorem checked11847 : checkPrefixCuts (2^48) 1556742145 9 Manual.Count131072.C011847.packed 128 cuts11847 = true := by
 decide +kernel
def pointBounds11847 : List (Nat × Nat × Nat) := [(1556784128,93155582914359,93155958719767),(1556833280,93156010512207,93156386317944)]
theorem point_links_checked11847 : (cuts11847.take 2).map (fun c => (1556742145-1+2*2^9*c.k,93155221660449+c.lower,93155597465585+c.upper)) = pointBounds11847 := by
 decide +kernel
def cuts11848 : List PrefixCut := [⟨9,74668110,74668168⟩,
⟨57,501877367,501877756⟩,
⟨105,919129980,919130692⟩,
⟨128,1117627640,1117628507⟩]
theorem checked11848 : checkPrefixCuts (2^48) 1556873217 9 Manual.Count131072.C011848.packed 128 cuts11848 = true := by
 decide +kernel
def pointBounds11848 : List (Nat × Nat × Nat) := [(1556882432,93156418570526,93156794376577),(1556931584,93156845779783,93157221586165),(1556980736,93157263032396,93157638839101)]
theorem point_links_checked11848 : (cuts11848.take 3).map (fun c => (1556873217-1+2*2^9*c.k,93156343902416+c.lower,93156719708409+c.upper)) = pointBounds11848 := by
 decide +kernel
def cuts11849 : List PrefixCut := [⟨25,220730233,220730401⟩,
⟨73,635425585,635426074⟩,
⟨121,1052638636,1052639450⟩,
⟨128,1110302655,1110303515⟩]
theorem checked11849 : checkPrefixCuts (2^48) 1557004289 9 Manual.Count131072.C011849.packed 128 cuts11849 = true := by
 decide +kernel
def pointBounds11849 : List (Nat × Nat × Nat) := [(1557029888,93157682260289,93158058067317),(1557079040,93158096955641,93158472762990),(1557128192,93158514168692,93158889976366)]
theorem point_links_checked11849 : (cuts11849.take 3).map (fun c => (1557004289-1+2*2^9*c.k,93157461530056+c.lower,93157837336916+c.upper)) = pointBounds11849 := by
 decide +kernel
def cuts11850 : List PrefixCut := [⟨41,353209098,353209370⟩,
⟨89,772745625,772746225⟩,
⟨128,1117258292,1117259157⟩]
theorem checked11850 : checkPrefixCuts (2^48) 1557135361 9 Manual.Count131072.C011850.packed 128 cuts11850 = true := by
 decide +kernel
def pointBounds11850 : List (Nat × Nat × Nat) := [(1557177344,93158925041809,93159300849801),(1557226496,93159344578336,93159720386656)]
theorem point_links_checked11850 : (cuts11850.take 2).map (fun c => (1557135361-1+2*2^9*c.k,93158571832711+c.lower,93158947640431+c.upper)) = pointBounds11850 := by
 decide +kernel
def cuts11851 : List PrefixCut := [⟨9,83867435,83867499⟩,
⟨57,500124001,500124383⟩,
⟨105,911306863,911307566⟩,
⟨128,1111381053,1111381909⟩]
theorem checked11851 : checkPrefixCuts (2^48) 1557266433 9 Manual.Count131072.C011851.packed 128 cuts11851 = true := by
 decide +kernel
def pointBounds11851 : List (Nat × Nat × Nat) := [(1557275648,93159772958438,93160148767087),(1557324800,93160189215004,93160565023971),(1557373952,93160600397866,93160976207154)]
theorem point_links_checked11851 : (cuts11851.take 3).map (fun c => (1557266433-1+2*2^9*c.k,93159689091003+c.lower,93160064899588+c.upper)) = pointBounds11851 := by
 decide +kernel
def cuts11852 : List PrefixCut := [⟨25,224831387,224831562⟩,
⟨73,644843970,644844474⟩,
⟨121,1065023929,1065024754⟩,
⟨128,1126287781,1126288652⟩]
theorem checked11852 : checkPrefixCuts (2^48) 1557397505 9 Manual.Count131072.C011852.packed 128 cuts11852 = true := by
 decide +kernel
def pointBounds11852 : List (Nat × Nat × Nat) := [(1557423104,93161025303443,93161401113059),(1557472256,93161445316026,93161821125971),(1557521408,93161865495985,93162241306251)]
theorem point_links_checked11852 : (cuts11852.take 3).map (fun c => (1557397505-1+2*2^9*c.k,93160800472056+c.lower,93161176281497+c.upper)) = pointBounds11852 := by
 decide +kernel
def cuts11853 : List PrefixCut := [⟨41,357818593,357818877⟩,
⟨89,777972053,777972663⟩,
⟨128,1118783626,1118784499⟩]
theorem checked11853 : checkPrefixCuts (2^48) 1557528577 9 Manual.Count131072.C011853.packed 128 cuts11853 = true := by
 decide +kernel
def pointBounds11853 : List (Nat × Nat × Nat) := [(1557570560,93162284578430,93162660389026),(1557619712,93162704731890,93163080542812)]
theorem point_links_checked11853 : (cuts11853.take 2).map (fun c => (1557528577-1+2*2^9*c.k,93161926759837+c.lower,93162302570149+c.upper)) = pointBounds11853 := by
 decide +kernel
def cuts11854 : List PrefixCut := [⟨9,80593604,80593667⟩,
⟨57,506322278,506322668⟩,
⟨105,919750273,919750982⟩,
⟨128,1118509117,1118509981⟩]
theorem checked11854 : checkPrefixCuts (2^48) 1557659649 9 Manual.Count131072.C011854.packed 128 cuts11854 = true := by
 decide +kernel
def pointBounds11854 : List (Nat × Nat × Nat) := [(1557668864,93163126137067,93163501948315),(1557718016,93163551865741,93163927677316),(1557767168,93163965293736,93164341105630)]
theorem point_links_checked11854 : (cuts11854.take 3).map (fun c => (1557659649-1+2*2^9*c.k,93163045543463+c.lower,93163421354648+c.upper)) = pointBounds11854 := by
 decide +kernel
def cuts11855 : List PrefixCut := [⟨25,215017549,215017714⟩,
⟨73,641067351,641067843⟩,
⟨121,1062948071,1062948890⟩,
⟨128,1123112416,1123113280⟩]
theorem checked11855 : checkPrefixCuts (2^48) 1557790721 9 Manual.Count131072.C011855.packed 128 cuts11855 = true := by
 decide +kernel
def pointBounds11855 : List (Nat × Nat × Nat) := [(1557816320,93164379070129,93164754882343),(1557865472,93164805119931,93165180932472),(1557914624,93165227000651,93165602813519)]
theorem point_links_checked11855 : (cuts11855.take 3).map (fun c => (1557790721-1+2*2^9*c.k,93164164052580+c.lower,93164539864629+c.upper)) = pointBounds11855 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000057
