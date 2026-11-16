import PlattAssemblyKernel
import PlattCertificates.Count131072.C033840
import PlattCertificates.Count131072.C033841
import PlattCertificates.Count131072.C033842
import PlattCertificates.Count131072.C033843
import PlattCertificates.Count131072.C033844
import PlattCertificates.Count131072.C033845
import PlattCertificates.Count131072.C033846
import PlattCertificates.Count131072.C033847
import PlattCertificates.Count131072.C033848
import PlattCertificates.Count131072.C033849
import PlattCertificates.Count131072.C033850
import PlattCertificates.Count131072.C033851
import PlattCertificates.Count131072.C033852
import PlattCertificates.Count131072.C033853
import PlattCertificates.Count131072.C033854
import PlattCertificates.Count131072.C033855
import PlattCertificates.Count131072.C033856
import PlattCertificates.Count131072.C033857
import PlattCertificates.Count131072.C033858
import PlattCertificates.Count131072.C033859
import PlattCertificates.Count131072.C033860
import PlattCertificates.Count131072.C033861
import PlattCertificates.Count131072.C033862
import PlattCertificates.Count131072.C033863
import PlattCertificates.Count131072.C033864
import PlattCertificates.Count131072.C033865
import PlattCertificates.Count131072.C033866
import PlattCertificates.Count131072.C033867
import PlattCertificates.Count131072.C033868
import PlattCertificates.Count131072.C033869
import PlattCertificates.Count131072.C033870
import PlattCertificates.Count131072.C033871
namespace ChenEffective.PlattWindow.Assembly.Prefix.S4.B000120
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts33840 : List PrefixCut := [⟨1,5579523,5579527⟩,
⟨64,371476701,371476937⟩]
theorem checked33840 : checkPrefixCuts (2^48) 4439408641 10 Manual.Count131072.C033840.packed 64 cuts33840 = true := by
 decide +kernel
def pointBounds33840 : List (Nat × Nat × Nat) := [(4439410688,106756855184345,106757239399280)]
theorem point_links_checked33840 : (cuts33840.take 1).map (fun c => (4439408641-1+2*2^10*c.k,106756849604822+c.lower,106757233819753+c.upper)) = pointBounds33840 := by
 decide +kernel
def cuts33841 : List PrefixCut := [⟨5,28467383,28467402⟩,
⟨64,368866311,368866547⟩]
theorem checked33841 : checkPrefixCuts (2^48) 4439539713 10 Manual.Count131072.C033841.packed 64 cuts33841 = true := by
 decide +kernel
def pointBounds33841 : List (Nat × Nat × Nat) := [(4439549952,106757249548906,106757633764092)]
theorem point_links_checked33841 : (cuts33841.take 1).map (fun c => (4439539713-1+2*2^10*c.k,106757221081523+c.lower,106757605296690+c.upper)) = pointBounds33841 := by
 decide +kernel
def cuts33842 : List PrefixCut := [⟨9,50973453,50973486⟩,
⟨64,375385518,375385759⟩]
theorem checked33842 : checkPrefixCuts (2^48) 4439670785 10 Manual.Count131072.C033842.packed 64 cuts33842 = true := by
 decide +kernel
def pointBounds33842 : List (Nat × Nat × Nat) := [(4439689216,106757640921287,106758025136723)]
theorem point_links_checked33842 : (cuts33842.take 1).map (fun c => (4439670785-1+2*2^10*c.k,106757589947834+c.lower,106757974163237+c.upper)) = pointBounds33842 := by
 decide +kernel
def cuts33843 : List PrefixCut := [⟨13,76331054,76331102⟩,
⟨64,373282390,373282622⟩]
theorem checked33843 : checkPrefixCuts (2^48) 4439801857 10 Manual.Count131072.C033843.packed 64 cuts33843 = true := by
 decide +kernel
def pointBounds33843 : List (Nat × Nat × Nat) := [(4439828480,106758041664406,106758425880098)]
theorem point_links_checked33843 : (cuts33843.take 1).map (fun c => (4439801857-1+2*2^10*c.k,106757965333352+c.lower,106758349548996+c.upper)) = pointBounds33843 := by
 decide +kernel
def cuts33844 : List PrefixCut := [⟨17,98453921,98453985⟩,
⟨64,370735527,370735767⟩]
theorem checked33844 : checkPrefixCuts (2^48) 4439932929 10 Manual.Count131072.C033844.packed 64 cuts33844 = true := by
 decide +kernel
def pointBounds33844 : List (Nat × Nat × Nat) := [(4439967744,106758437069663,106758821285603)]
theorem point_links_checked33844 : (cuts33844.take 1).map (fun c => (4439932929-1+2*2^10*c.k,106758338615742+c.lower,106758722831618+c.upper)) = pointBounds33844 := by
 decide +kernel
def cuts33845 : List PrefixCut := [⟨21,120702222,120702300⟩,
⟨64,372753130,372753367⟩]
theorem checked33845 : checkPrefixCuts (2^48) 4440064001 10 Manual.Count131072.C033845.packed 64 cuts33845 = true := by
 decide +kernel
def pointBounds33845 : List (Nat × Nat × Nat) := [(4440107008,106758830053491,106759214269685)]
theorem point_links_checked33845 : (cuts33845.take 1).map (fun c => (4440064001-1+2*2^10*c.k,106758709351269+c.lower,106759093567385+c.upper)) = pointBounds33845 := by
 decide +kernel
def cuts33846 : List PrefixCut := [⟨25,149922297,149922391⟩,
⟨64,375531455,375531695⟩]
theorem checked33846 : checkPrefixCuts (2^48) 4440195073 10 Manual.Count131072.C033846.packed 64 cuts33846 = true := by
 decide +kernel
def pointBounds33846 : List (Nat × Nat × Nat) := [(4440246272,106759232026696,106759616243143)]
theorem point_links_checked33846 : (cuts33846.take 1).map (fun c => (4440195073-1+2*2^10*c.k,106759082104399+c.lower,106759466320752+c.upper)) = pointBounds33846 := by
 decide +kernel
def cuts33847 : List PrefixCut := [⟨29,168047305,168047414⟩,
⟨64,370258946,370259186⟩]
theorem checked33847 : checkPrefixCuts (2^48) 4440326145 10 Manual.Count131072.C033847.packed 64 cuts33847 = true := by
 decide +kernel
def pointBounds33847 : List (Nat × Nat × Nat) := [(4440385536,106759625683159,106760009899861)]
theorem point_links_checked33847 : (cuts33847.take 1).map (fun c => (4440326145-1+2*2^10*c.k,106759457635854+c.lower,106759841852447+c.upper)) = pointBounds33847 := by
 decide +kernel
def cuts33848 : List PrefixCut := [⟨33,193587671,193587792⟩,
⟨64,371515828,371516066⟩]
theorem checked33848 : checkPrefixCuts (2^48) 4440457217 10 Manual.Count131072.C033848.packed 64 cuts33848 = true := by
 decide +kernel
def pointBounds33848 : List (Nat × Nat × Nat) := [(4440524800,106760021482471,106760405699425)]
theorem point_links_checked33848 : (cuts33848.take 1).map (fun c => (4440457217-1+2*2^10*c.k,106759827894800+c.lower,106760212111633+c.upper)) = pointBounds33848 := by
 decide +kernel
def cuts33849 : List PrefixCut := [⟨37,218809535,218809674⟩,
⟨64,375434765,375435007⟩]
theorem checked33849 : checkPrefixCuts (2^48) 4440588289 10 Manual.Count131072.C033849.packed 64 cuts33849 = true := by
 decide +kernel
def pointBounds33849 : List (Nat × Nat × Nat) := [(4440664064,106760418220163,106760802437373)]
theorem point_links_checked33849 : (cuts33849.take 1).map (fun c => (4440588289-1+2*2^10*c.k,106760199410628+c.lower,106760583627699+c.upper)) = pointBounds33849 := by
 decide +kernel
def cuts33850 : List PrefixCut := [⟨41,237818177,237818325⟩,
⟨64,372191058,372191293⟩]
theorem checked33850 : checkPrefixCuts (2^48) 4440719361 10 Manual.Count131072.C033850.packed 64 cuts33850 = true := by
 decide +kernel
def pointBounds33850 : List (Nat × Nat × Nat) := [(4440803328,106760812663570,106761196881031)]
theorem point_links_checked33850 : (cuts33850.take 1).map (fun c => (4440719361-1+2*2^10*c.k,106760574845393+c.lower,106760959062706+c.upper)) = pointBounds33850 := by
 decide +kernel
def cuts33851 : List PrefixCut := [⟨45,263670963,263671129⟩,
⟨64,374968898,374969134⟩]
theorem checked33851 : checkPrefixCuts (2^48) 4440850433 10 Manual.Count131072.C033851.packed 64 cuts33851 = true := by
 decide +kernel
def pointBounds33851 : List (Nat × Nat × Nat) := [(4440942592,106761210707414,106761594925128)]
theorem point_links_checked33851 : (cuts33851.take 1).map (fun c => (4440850433-1+2*2^10*c.k,106760947036451+c.lower,106761331253999+c.upper)) = pointBounds33851 := by
 decide +kernel
def cuts33852 : List PrefixCut := [⟨49,283881360,283881537⟩,
⟨64,371091659,371091891⟩]
theorem checked33852 : checkPrefixCuts (2^48) 4440981505 10 Manual.Count131072.C033852.packed 64 cuts33852 = true := by
 decide +kernel
def pointBounds33852 : List (Nat × Nat × Nat) := [(4441081856,106761605886709,106761990104670)]
theorem point_links_checked33852 : (cuts33852.take 1).map (fun c => (4440981505-1+2*2^10*c.k,106761322005349+c.lower,106761706223133+c.upper)) = pointBounds33852 := by
 decide +kernel
def cuts33853 : List PrefixCut := [⟨53,307449527,307449723⟩,
⟨64,372601755,372601992⟩]
theorem checked33853 : checkPrefixCuts (2^48) 4441112577 10 Manual.Count131072.C033853.packed 64 cuts33853 = true := by
 decide +kernel
def pointBounds33853 : List (Nat × Nat × Nat) := [(4441221120,106762000546535,106762384764747)]
theorem point_links_checked33853 : (cuts33853.take 1).map (fun c => (4441112577-1+2*2^10*c.k,106761693097008+c.lower,106762077315024+c.upper)) = pointBounds33853 := by
 decide +kernel
def cuts33854 : List PrefixCut := [⟨57,330889571,330889778⟩,
⟨64,372210544,372210776⟩]
theorem checked33854 : checkPrefixCuts (2^48) 4441243649 10 Manual.Count131072.C033854.packed 64 cuts33854 = true := by
 decide +kernel
def pointBounds33854 : List (Nat × Nat × Nat) := [(4441360384,106762396588334,106762780806794)]
theorem point_links_checked33854 : (cuts33854.take 1).map (fun c => (4441243649-1+2*2^10*c.k,106762065698763+c.lower,106762449917016+c.upper)) = pointBounds33854 := by
 decide +kernel
def cuts33855 : List PrefixCut := [⟨61,361045838,361046071⟩,
⟨64,379360865,379361111⟩]
theorem checked33855 : checkPrefixCuts (2^48) 4441374721 10 Manual.Count131072.C033855.packed 64 cuts33855 = true := by
 decide +kernel
def pointBounds33855 : List (Nat × Nat × Nat) := [(4441499648,106762798955145,106763183173863)]
theorem point_links_checked33855 : (cuts33855.take 1).map (fun c => (4441374721-1+2*2^10*c.k,106762437909307+c.lower,106762822127792+c.upper)) = pointBounds33855 := by
 decide +kernel
def cuts33856 : List PrefixCut := [⟨64,373202486,373202723⟩]
theorem checked33856 : checkPrefixCuts (2^48) 4441505793 10 Manual.Count131072.C033856.packed 64 cuts33856 = true := by
 decide +kernel
def cuts33857 : List PrefixCut := [⟨1,5259865,5259868⟩,
⟨64,372557786,372558023⟩]
theorem checked33857 : checkPrefixCuts (2^48) 4441636865 10 Manual.Count131072.C033857.packed 64 cuts33857 = true := by
 decide +kernel
def pointBounds33857 : List (Nat × Nat × Nat) := [(4441638912,106763195732523,106763579951494)]
theorem point_links_checked33857 : (cuts33857.take 1).map (fun c => (4441636865-1+2*2^10*c.k,106763190472658+c.lower,106763574691626+c.upper)) = pointBounds33857 := by
 decide +kernel
def cuts33858 : List PrefixCut := [⟨5,29213542,29213560⟩,
⟨64,367604018,367604256⟩]
theorem checked33858 : checkPrefixCuts (2^48) 4441767937 10 Manual.Count131072.C033858.packed 64 cuts33858 = true := by
 decide +kernel
def pointBounds33858 : List (Nat × Nat × Nat) := [(4441778176,106763592243986,106763976463209)]
theorem point_links_checked33858 : (cuts33858.take 1).map (fun c => (4441767937-1+2*2^10*c.k,106763563030444+c.lower,106763947249649+c.upper)) = pointBounds33858 := by
 decide +kernel
def cuts33859 : List PrefixCut := [⟨9,52912286,52912319⟩,
⟨64,376654660,376654896⟩]
theorem checked33859 : checkPrefixCuts (2^48) 4441899009 10 Manual.Count131072.C033859.packed 64 cuts33859 = true := by
 decide +kernel
def pointBounds33859 : List (Nat × Nat × Nat) := [(4441917440,106763983546748,106764367766224)]
theorem point_links_checked33859 : (cuts33859.take 1).map (fun c => (4441899009-1+2*2^10*c.k,106763930634462+c.lower,106764314853905+c.upper)) = pointBounds33859 := by
 decide +kernel
def cuts33860 : List PrefixCut := [⟨13,75722471,75722520⟩,
⟨64,371384269,371384510⟩]
theorem checked33860 : checkPrefixCuts (2^48) 4442030081 10 Manual.Count131072.C033860.packed 64 cuts33860 = true := by
 decide +kernel
def pointBounds33860 : List (Nat × Nat × Nat) := [(4442056704,106764383011593,106764767231321)]
theorem point_links_checked33860 : (cuts33860.take 1).map (fun c => (4442030081-1+2*2^10*c.k,106764307289122+c.lower,106764691508801+c.upper)) = pointBounds33860 := by
 decide +kernel
def cuts33861 : List PrefixCut := [⟨17,98024351,98024415⟩,
⟨64,375998768,375999008⟩]
theorem checked33861 : checkPrefixCuts (2^48) 4442161153 10 Manual.Count131072.C033861.packed 64 cuts33861 = true := by
 decide +kernel
def pointBounds33861 : List (Nat × Nat × Nat) := [(4442195968,106764776697742,106765160917726)]
theorem point_links_checked33861 : (cuts33861.take 1).map (fun c => (4442161153-1+2*2^10*c.k,106764678673391+c.lower,106765062893311+c.upper)) = pointBounds33861 := by
 decide +kernel
def cuts33862 : List PrefixCut := [⟨21,124886954,124887034⟩,
⟨64,374973974,374974214⟩]
theorem checked33862 : checkPrefixCuts (2^48) 4442292225 10 Manual.Count131072.C033862.packed 64 cuts33862 = true := by
 decide +kernel
def pointBounds33862 : List (Nat × Nat × Nat) := [(4442335232,106765179559113,106765563779353)]
theorem point_links_checked33862 : (cuts33862.take 1).map (fun c => (4442292225-1+2*2^10*c.k,106765054672159+c.lower,106765438892319+c.upper)) = pointBounds33862 := by
 decide +kernel
def cuts33863 : List PrefixCut := [⟨25,148136381,148136471⟩,
⟨64,373632355,373632590⟩]
theorem checked33863 : checkPrefixCuts (2^48) 4442423297 10 Manual.Count131072.C033863.packed 64 cuts33863 = true := by
 decide +kernel
def pointBounds33863 : List (Nat × Nat × Nat) := [(4442474496,106765577782514,106765962003004)]
theorem point_links_checked33863 : (cuts33863.take 1).map (fun c => (4442423297-1+2*2^10*c.k,106765429646133+c.lower,106765813866533+c.upper)) = pointBounds33863 := by
 decide +kernel
def cuts33864 : List PrefixCut := [⟨29,166949322,166949423⟩,
⟨64,373367845,373368080⟩]
theorem checked33864 : checkPrefixCuts (2^48) 4442554369 10 Manual.Count131072.C033864.packed 64 cuts33864 = true := by
 decide +kernel
def pointBounds33864 : List (Nat × Nat × Nat) := [(4442613760,106765970227810,106766354448546)]
theorem point_links_checked33864 : (cuts33864.take 1).map (fun c => (4442554369-1+2*2^10*c.k,106765803278488+c.lower,106766187499123+c.upper)) = pointBounds33864 := by
 decide +kernel
def cuts33865 : List PrefixCut := [⟨33,192096729,192096853⟩,
⟨64,375194159,375194395⟩]
theorem checked33865 : checkPrefixCuts (2^48) 4442685441 10 Manual.Count131072.C033865.packed 64 cuts33865 = true := by
 decide +kernel
def pointBounds33865 : List (Nat × Nat × Nat) := [(4442753024,106766368743062,106766752964056)]
theorem point_links_checked33865 : (cuts33865.take 1).map (fun c => (4442685441-1+2*2^10*c.k,106766176646333+c.lower,106766560867203+c.upper)) = pointBounds33865 := by
 decide +kernel
def cuts33866 : List PrefixCut := [⟨37,216165601,216165738⟩,
⟨64,375119751,375119987⟩]
theorem checked33866 : checkPrefixCuts (2^48) 4442816513 10 Manual.Count131072.C033866.packed 64 cuts33866 = true := by
 decide +kernel
def pointBounds33866 : List (Nat × Nat × Nat) := [(4442892288,106766768006093,106767152227336)]
theorem point_links_checked33866 : (cuts33866.take 1).map (fun c => (4442816513-1+2*2^10*c.k,106766551840492+c.lower,106766936061598+c.upper)) = pointBounds33866 := by
 decide +kernel
def cuts33867 : List PrefixCut := [⟨41,242830482,242830632⟩,
⟨64,375235427,375235660⟩]
theorem checked33867 : checkPrefixCuts (2^48) 4442947585 10 Manual.Count131072.C033867.packed 64 cuts33867 = true := by
 decide +kernel
def pointBounds33867 : List (Nat × Nat × Nat) := [(4443031552,106767169790725,106767554012217)]
theorem point_links_checked33867 : (cuts33867.take 1).map (fun c => (4442947585-1+2*2^10*c.k,106766926960243+c.lower,106767311181585+c.upper)) = pointBounds33867 := by
 decide +kernel
def cuts33868 : List PrefixCut := [⟨45,263728777,263728938⟩,
⟨64,375034245,375034476⟩]
theorem checked33868 : checkPrefixCuts (2^48) 4443078657 10 Manual.Count131072.C033868.packed 64 cuts33868 = true := by
 decide +kernel
def pointBounds33868 : List (Nat × Nat × Nat) := [(4443170816,106767565924447,106767950146183)]
theorem point_links_checked33868 : (cuts33868.take 1).map (fun c => (4443078657-1+2*2^10*c.k,106767302195670+c.lower,106767686417245+c.upper)) = pointBounds33868 := by
 decide +kernel
def cuts33869 : List PrefixCut := [⟨49,288933560,288933741⟩,
⟨64,376036785,376037021⟩]
theorem checked33869 : checkPrefixCuts (2^48) 4443209729 10 Manual.Count131072.C033869.packed 64 cuts33869 = true := by
 decide +kernel
def pointBounds33869 : List (Nat × Nat × Nat) := [(4443310080,106767966163475,106768350385462)]
theorem point_links_checked33869 : (cuts33869.take 1).map (fun c => (4443209729-1+2*2^10*c.k,106767677229915+c.lower,106768061451721+c.upper)) = pointBounds33869 := by
 decide +kernel
def cuts33870 : List PrefixCut := [⟨53,313186624,313186819⟩,
⟨64,377736071,377736304⟩]
theorem checked33870 : checkPrefixCuts (2^48) 4443340801 10 Manual.Count131072.C033870.packed 64 cuts33870 = true := by
 decide +kernel
def pointBounds33870 : List (Nat × Nat × Nat) := [(4443449344,106768366453324,106768750675561)]
theorem point_links_checked33870 : (cuts33870.take 1).map (fun c => (4443340801-1+2*2^10*c.k,106768053266700+c.lower,106768437488742+c.upper)) = pointBounds33870 := by
 decide +kernel
def cuts33871 : List PrefixCut := [⟨57,330470221,330470428⟩,
⟨64,372277225,372277457⟩]
theorem checked33871 : checkPrefixCuts (2^48) 4443471873 10 Manual.Count131072.C033871.packed 64 cuts33871 = true := by
 decide +kernel
def pointBounds33871 : List (Nat × Nat × Nat) := [(4443588608,106768761472992,106769145695474)]
theorem point_links_checked33871 : (cuts33871.take 1).map (fun c => (4443471873-1+2*2^10*c.k,106768431002771+c.lower,106768815225046+c.upper)) = pointBounds33871 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S4.B000120
