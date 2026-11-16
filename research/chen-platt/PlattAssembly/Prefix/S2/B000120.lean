import PlattAssemblyKernel
import PlattCertificates.Count131072.C013840
import PlattCertificates.Count131072.C013841
import PlattCertificates.Count131072.C013842
import PlattCertificates.Count131072.C013843
import PlattCertificates.Count131072.C013844
import PlattCertificates.Count131072.C013845
import PlattCertificates.Count131072.C013846
import PlattCertificates.Count131072.C013847
import PlattCertificates.Count131072.C013848
import PlattCertificates.Count131072.C013849
import PlattCertificates.Count131072.C013850
import PlattCertificates.Count131072.C013851
import PlattCertificates.Count131072.C013852
import PlattCertificates.Count131072.C013853
import PlattCertificates.Count131072.C013854
import PlattCertificates.Count131072.C013855
import PlattCertificates.Count131072.C013856
import PlattCertificates.Count131072.C013857
import PlattCertificates.Count131072.C013858
import PlattCertificates.Count131072.C013859
import PlattCertificates.Count131072.C013860
import PlattCertificates.Count131072.C013861
import PlattCertificates.Count131072.C013862
import PlattCertificates.Count131072.C013863
import PlattCertificates.Count131072.C013864
import PlattCertificates.Count131072.C013865
import PlattCertificates.Count131072.C013866
import PlattCertificates.Count131072.C013867
import PlattCertificates.Count131072.C013868
import PlattCertificates.Count131072.C013869
import PlattCertificates.Count131072.C013870
import PlattCertificates.Count131072.C013871
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000120
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts13840 : List PrefixCut := [⟨19,139964967,139965065⟩,
⟨75,562483097,562483491⟩,
⟨128,950772786,950773454⟩]
theorem checked13840 : checkPrefixCuts (2^48) 1817968641 9 Manual.Count131072.C013840.packed 128 cuts13840 = true := by
 decide +kernel
def pointBounds13840 : List (Nat × Nat × Nat) := [(1817988096,95210688638908,95211065951728),(1818045440,95211111157038,95211488470154)]
theorem point_links_checked13840 : (cuts13840.take 2).map (fun c => (1817968641-1+2*2^9*c.k,95210548673941+c.lower,95210925986663+c.upper)) = pointBounds13840 := by
 decide +kernel
def cuts13841 : List PrefixCut := [⟨3,21519707,21519721⟩,
⟨59,437508832,437509135⟩,
⟨115,847137660,847138252⟩,
⟨128,941725093,941725753⟩]
theorem checked13841 : checkPrefixCuts (2^48) 1818099713 9 Manual.Count131072.C013841.packed 128 cuts13841 = true := by
 decide +kernel
def pointBounds13841 : List (Nat × Nat × Nat) := [(1818102784,95211520966434,95211898279838),(1818160128,95211936955559,95212314269252),(1818217472,95212346584387,95212723898369)]
theorem point_links_checked13841 : (cuts13841.take 3).map (fun c => (1818099713-1+2*2^9*c.k,95211499446727+c.lower,95211876760117+c.upper)) = pointBounds13841 := by
 decide +kernel
def cuts13842 : List PrefixCut := [⟨43,317350492,317350712⟩,
⟨99,732835912,732836425⟩,
⟨128,949242269,949242933⟩]
theorem checked13842 : checkPrefixCuts (2^48) 1818230785 9 Manual.Count131072.C013842.packed 128 cuts13842 = true := by
 decide +kernel
def pointBounds13842 : List (Nat × Nat × Nat) := [(1818274816,95212758522312,95213135836582),(1818332160,95213174007732,95213551322295)]
theorem point_links_checked13842 : (cuts13842.take 2).map (fun c => (1818230785-1+2*2^9*c.k,95212441171820+c.lower,95212818485870+c.upper)) = pointBounds13842 := by
 decide +kernel
def cuts13843 : List PrefixCut := [⟨27,195041294,195041434⟩,
⟨83,619633271,619633702⟩,
⟨128,951031520,951032181⟩]
theorem checked13843 : checkPrefixCuts (2^48) 1818361857 9 Manual.Count131072.C013843.packed 128 cuts13843 = true := by
 decide +kernel
def pointBounds13843 : List (Nat × Nat × Nat) := [(1818389504,95213585455383,95213962770237),(1818446848,95214010047360,95214387362505)]
theorem point_links_checked13843 : (cuts13843.take 2).map (fun c => (1818361857-1+2*2^9*c.k,95213390414089+c.lower,95213767728803+c.upper)) = pointBounds13843 := by
 decide +kernel
def cuts13844 : List PrefixCut := [⟨11,78320813,78320868⟩,
⟨67,502111922,502112274⟩,
⟨123,914900601,914901246⟩,
⟨128,951581984,951582654⟩]
theorem checked13844 : checkPrefixCuts (2^48) 1818492929 9 Manual.Count131072.C013844.packed 128 cuts13844 = true := by
 decide +kernel
def pointBounds13844 : List (Nat × Nat × Nat) := [(1818504192,95214419766422,95214797081852),(1818561536,95214843557531,95215220873258),(1818618880,95215256346210,95215633662230)]
theorem point_links_checked13844 : (cuts13844.take 3).map (fun c => (1818492929-1+2*2^9*c.k,95214341445609+c.lower,95214718760984+c.upper)) = pointBounds13844 := by
 decide +kernel
def cuts13845 : List PrefixCut := [⟨51,371760679,371760942⟩,
⟨107,792106896,792107453⟩,
⟨128,944703508,944704175⟩]
theorem checked13845 : checkPrefixCuts (2^48) 1818624001 9 Manual.Count131072.C013845.packed 128 cuts13845 = true := by
 decide +kernel
def pointBounds13845 : List (Nat × Nat × Nat) := [(1818676224,95215664788272,95216042104580),(1818733568,95216085134489,95216462451091)]
theorem point_links_checked13845 : (cuts13845.take 2).map (fun c => (1818624001-1+2*2^9*c.k,95215293027593+c.lower,95215670343638+c.upper)) = pointBounds13845 := by
 decide +kernel
def cuts13846 : List PrefixCut := [⟨35,255355420,255355599⟩,
⟨91,673198961,673199430⟩,
⟨128,940457121,940457784⟩]
theorem checked13846 : checkPrefixCuts (2^48) 1818755073 9 Manual.Count131072.C013846.packed 128 cuts13846 = true := by
 decide +kernel
def pointBounds13846 : List (Nat × Nat × Nat) := [(1818790912,95216493086521,95216870403412),(1818848256,95216910930062,95217288247243)]
theorem point_links_checked13846 : (cuts13846.take 2).map (fun c => (1818755073-1+2*2^9*c.k,95216237731101+c.lower,95216615047813+c.upper)) = pointBounds13846 := by
 decide +kernel
def cuts13847 : List PrefixCut := [⟨19,142060900,142060998⟩,
⟨75,562508848,562509239⟩,
⟨128,957875642,957876310⟩]
theorem checked13847 : checkPrefixCuts (2^48) 1818886145 9 Manual.Count131072.C013847.packed 128 cuts13847 = true := by
 decide +kernel
def pointBounds13847 : List (Nat × Nat × Nat) := [(1818905600,95217320249122,95217697566595),(1818962944,95217740697070,95218118014836)]
theorem point_links_checked13847 : (cuts13847.take 2).map (fun c => (1818886145-1+2*2^9*c.k,95217178188222+c.lower,95217555505597+c.upper)) = pointBounds13847 := by
 decide +kernel
def cuts13848 : List PrefixCut := [⟨3,20889894,20889908⟩,
⟨59,440537660,440537968⟩,
⟨115,851816671,851817266⟩,
⟨128,947439501,947440163⟩]
theorem checked13848 : checkPrefixCuts (2^48) 1819017217 9 Manual.Count131072.C013848.packed 128 cuts13848 = true := by
 decide +kernel
def pointBounds13848 : List (Nat × Nat × Nat) := [(1819020288,95218156953758,95218534271815),(1819077632,95218576601524,95218953919875),(1819134976,95218987880535,95219365199173)]
theorem point_links_checked13848 : (cuts13848.take 3).map (fun c => (1819017217-1+2*2^9*c.k,95218136063864+c.lower,95218513381907+c.upper)) = pointBounds13848 := by
 decide +kernel
def cuts13849 : List PrefixCut := [⟨43,315024244,315024468⟩,
⟨99,733703988,733704502⟩,
⟨128,947680399,947681064⟩]
theorem checked13849 : checkPrefixCuts (2^48) 1819148289 9 Manual.Count131072.C013849.packed 128 cuts13849 = true := by
 decide +kernel
def pointBounds13849 : List (Nat × Nat × Nat) := [(1819192320,95219398527609,95219775846538),(1819249664,95219817207353,95220194526572)]
theorem point_links_checked13849 : (cuts13849.take 2).map (fun c => (1819148289-1+2*2^9*c.k,95219083503365+c.lower,95219460822070+c.upper)) = pointBounds13849 := by
 decide +kernel
def cuts13850 : List PrefixCut := [⟨27,194478771,194478907⟩,
⟨83,603385245,603385669⟩,
⟨128,936627580,936628241⟩]
theorem checked13850 : checkPrefixCuts (2^48) 1819279361 9 Manual.Count131072.C013850.packed 128 cuts13850 = true := by
 decide +kernel
def pointBounds13850 : List (Nat × Nat × Nat) := [(1819307008,95220225662535,95220602982041),(1819364352,95220634569009,95221011888803)]
theorem point_links_checked13850 : (cuts13850.take 2).map (fun c => (1819279361-1+2*2^9*c.k,95220031183764+c.lower,95220408503134+c.upper)) = pointBounds13850 := by
 decide +kernel
def cuts13851 : List PrefixCut := [⟨11,86016640,86016699⟩,
⟨67,498610267,498610615⟩,
⟨123,921091592,921092234⟩,
⟨128,961621867,961622537⟩]
theorem checked13851 : checkPrefixCuts (2^48) 1819410433 9 Manual.Count131072.C013851.packed 128 cuts13851 = true := by
 decide +kernel
def pointBounds13851 : List (Nat × Nat × Nat) := [(1819421696,95221053827984,95221431148074),(1819479040,95221466421611,95221843741990),(1819536384,95221888902936,95222266223609)]
theorem point_links_checked13851 : (cuts13851.take 3).map (fun c => (1819410433-1+2*2^9*c.k,95220967811344+c.lower,95221345131375+c.upper)) = pointBounds13851 := by
 decide +kernel
def cuts13852 : List PrefixCut := [⟨51,380390692,380390954⟩,
⟨107,797585876,797586430⟩,
⟨128,951497737,951498395⟩]
theorem checked13852 : checkPrefixCuts (2^48) 1819541505 9 Manual.Count131072.C013852.packed 128 cuts13852 = true := by
 decide +kernel
def pointBounds13852 : List (Nat × Nat × Nat) := [(1819593728,95222309823903,95222687144866),(1819651072,95222727019087,95223104340342)]
theorem point_links_checked13852 : (cuts13852.take 2).map (fun c => (1819541505-1+2*2^9*c.k,95221929433211+c.lower,95222306753912+c.upper)) = pointBounds13852 := by
 decide +kernel
def cuts13853 : List PrefixCut := [⟨35,258939114,258939296⟩,
⟨91,679510945,679511419⟩,
⟨128,958080274,958080943⟩]
theorem checked13853 : checkPrefixCuts (2^48) 1819672577 9 Manual.Count131072.C013853.packed 128 cuts13853 = true := by
 decide +kernel
def pointBounds13853 : List (Nat × Nat × Nat) := [(1819708416,95223139870062,95223517191603),(1819765760,95223560441893,95223937763726)]
theorem point_links_checked13853 : (cuts13853.take 2).map (fun c => (1819672577-1+2*2^9*c.k,95222880930948+c.lower,95223258252307+c.upper)) = pointBounds13853 := by
 decide +kernel
def cuts13854 : List PrefixCut := [⟨19,138122431,138122529⟩,
⟨75,555110399,555110785⟩,
⟨128,957856396,957857063⟩]
theorem checked13854 : checkPrefixCuts (2^48) 1819803649 9 Manual.Count131072.C013854.packed 128 cuts13854 = true := by
 decide +kernel
def pointBounds13854 : List (Nat × Nat × Nat) := [(1819823104,95223977133653,95224354455779),(1819880448,95224394121621,95224771444035)]
theorem point_links_checked13854 : (cuts13854.take 2).map (fun c => (1819803649-1+2*2^9*c.k,95223839011222+c.lower,95224216333250+c.upper)) = pointBounds13854 := by
 decide +kernel
def cuts13855 : List PrefixCut := [⟨3,23663276,23663294⟩,
⟨59,443099507,443099816⟩,
⟨115,858346871,858347470⟩,
⟨128,952838935,952839602⟩]
theorem checked13855 : checkPrefixCuts (2^48) 1819934721 9 Manual.Count131072.C013855.packed 128 cuts13855 = true := by
 decide +kernel
def pointBounds13855 : List (Nat × Nat × Nat) := [(1819937792,95224820530894,95225197853607),(1819995136,95225239967125,95225617290129),(1820052480,95225655214489,95226032537783)]
theorem point_links_checked13855 : (cuts13855.take 3).map (fun c => (1819934721-1+2*2^9*c.k,95224796867618+c.lower,95225174190313+c.upper)) = pointBounds13855 := by
 decide +kernel
def cuts13856 : List PrefixCut := [⟨43,318577050,318577269⟩,
⟨99,734880743,734881253⟩,
⟨128,944728680,944729335⟩]
theorem checked13856 : checkPrefixCuts (2^48) 1820065793 9 Manual.Count131072.C013856.packed 128 cuts13856 = true := by
 decide +kernel
def pointBounds13856 : List (Nat × Nat × Nat) := [(1820109824,95226068283603,95226445607184),(1820167168,95226484587296,95226861911168)]
theorem point_links_checked13856 : (cuts13856.take 2).map (fun c => (1820065793-1+2*2^9*c.k,95225749706553+c.lower,95226127029915+c.upper)) = pointBounds13856 := by
 decide +kernel
def cuts13857 : List PrefixCut := [⟨27,206133290,206133432⟩,
⟨83,621328355,621328786⟩,
⟨128,940949797,940950455⟩]
theorem checked13857 : checkPrefixCuts (2^48) 1820196865 9 Manual.Count131072.C013857.packed 128 cuts13857 = true := by
 decide +kernel
def pointBounds13857 : List (Nat × Nat × Nat) := [(1820224512,95226900568523,95227277892682),(1820281856,95227315763588,95227693088036)]
theorem point_links_checked13857 : (cuts13857.take 2).map (fun c => (1820196865-1+2*2^9*c.k,95226694435233+c.lower,95227071759250+c.upper)) = pointBounds13857 := by
 decide +kernel
def cuts13858 : List PrefixCut := [⟨11,83344593,83344651⟩,
⟨67,500214405,500214756⟩,
⟨123,915988641,915989279⟩,
⟨128,952787664,952788328⟩]
theorem checked13858 : checkPrefixCuts (2^48) 1820327937 9 Manual.Count131072.C013858.packed 128 cuts13858 = true := by
 decide +kernel
def pointBounds13858 : List (Nat × Nat × Nat) := [(1820339200,95227718729623,95228096054356),(1820396544,95228135599435,95228512924461),(1820453888,95228551373671,95228928698984)]
theorem point_links_checked13858 : (cuts13858.take 3).map (fun c => (1820327937-1+2*2^9*c.k,95227635385030+c.lower,95228012709705+c.upper)) = pointBounds13858 := by
 decide +kernel
def cuts13859 : List PrefixCut := [⟨51,381899863,381900122⟩,
⟨107,788062113,788062652⟩,
⟨128,945606972,945607623⟩]
theorem checked13859 : checkPrefixCuts (2^48) 1820459009 9 Manual.Count131072.C013859.packed 128 cuts13859 = true := by
 decide +kernel
def pointBounds13859 : List (Nat × Nat × Nat) := [(1820511232,95228970072557,95229347398155),(1820568576,95229376234807,95229753560685)]
theorem point_links_checked13859 : (cuts13859.take 2).map (fun c => (1820459009-1+2*2^9*c.k,95228588172694+c.lower,95228965498033+c.upper)) = pointBounds13859 := by
 decide +kernel
def cuts13860 : List PrefixCut := [⟨35,260818411,260818596⟩,
⟨91,674530441,674530916⟩,
⟨128,949403709,949404374⟩]
theorem checked13860 : checkPrefixCuts (2^48) 1820590081 9 Manual.Count131072.C013860.packed 128 cuts13860 = true := by
 decide +kernel
def pointBounds13860 : List (Nat × Nat × Nat) := [(1820625920,95229794598077,95230171924252),(1820683264,95230208310107,95230585636572)]
theorem point_links_checked13860 : (cuts13860.take 2).map (fun c => (1820590081-1+2*2^9*c.k,95229533779666+c.lower,95229911105656+c.upper)) = pointBounds13860 := by
 decide +kernel
def cuts13861 : List PrefixCut := [⟨19,139289610,139289708⟩,
⟨75,550965931,550966312⟩,
⟨128,938977902,938978559⟩]
theorem checked13861 : checkPrefixCuts (2^48) 1820721153 9 Manual.Count131072.C013861.packed 128 cuts13861 = true := by
 decide +kernel
def pointBounds13861 : List (Nat × Nat × Nat) := [(1820740608,95230622472985,95230999799738),(1820797952,95231034149306,95231411476342)]
theorem point_links_checked13861 : (cuts13861.take 2).map (fun c => (1820721153-1+2*2^9*c.k,95230483183375+c.lower,95230860510030+c.upper)) = pointBounds13861 := by
 decide +kernel
def cuts13862 : List PrefixCut := [⟨3,22878434,22878450⟩,
⟨59,440712170,440712474⟩,
⟨115,858378124,858378714⟩,
⟨128,961169558,961170220⟩]
theorem checked13862 : checkPrefixCuts (2^48) 1820852225 9 Manual.Count131072.C013862.packed 128 cuts13862 = true := by
 decide +kernel
def pointBounds13862 : List (Nat × Nat × Nat) := [(1820855296,95231445039711,95231822367039),(1820912640,95231862873447,95232240201063),(1820969984,95232280539401,95232657867303)]
theorem point_links_checked13862 : (cuts13862.take 3).map (fun c => (1820852225-1+2*2^9*c.k,95231422161277+c.lower,95231799488589+c.upper)) = pointBounds13862 := by
 decide +kernel
def cuts13863 : List PrefixCut := [⟨43,319653088,319653308⟩,
⟨99,732037327,732037838⟩,
⟨128,947343749,947344411⟩]
theorem checked13863 : checkPrefixCuts (2^48) 1820983297 9 Manual.Count131072.C013863.packed 128 cuts13863 = true := by
 decide +kernel
def pointBounds13863 : List (Nat × Nat × Nat) := [(1821027328,95232702983923,95233080312117),(1821084672,95233115368162,95233492696647)]
theorem point_links_checked13863 : (cuts13863.take 2).map (fun c => (1820983297-1+2*2^9*c.k,95232383330835+c.lower,95232760658809+c.upper)) = pointBounds13863 := by
 decide +kernel
def cuts13864 : List PrefixCut := [⟨27,197992314,197992451⟩,
⟨83,610505228,610505656⟩,
⟨128,941557185,941557849⟩]
theorem checked13864 : checkPrefixCuts (2^48) 1821114369 9 Manual.Count131072.C013864.packed 128 cuts13864 = true := by
 decide +kernel
def pointBounds13864 : List (Nat × Nat × Nat) := [(1821142016,95233528666898,95233905995671),(1821199360,95233941179812,95234318508876)]
theorem point_links_checked13864 : (cuts13864.take 2).map (fun c => (1821114369-1+2*2^9*c.k,95233330674584+c.lower,95233708003220+c.upper)) = pointBounds13864 := by
 decide +kernel
def cuts13865 : List PrefixCut := [⟨11,77120592,77120645⟩,
⟨67,501353226,501353573⟩,
⟨123,917072503,917073138⟩,
⟨128,954162070,954162730⟩]
theorem checked13865 : checkPrefixCuts (2^48) 1821245441 9 Manual.Count131072.C013865.packed 128 cuts13865 = true := by
 decide +kernel
def pointBounds13865 : List (Nat × Nat × Nat) := [(1821256704,95234349352361,95234726681714),(1821314048,95234773584995,95235150914642),(1821371392,95235189304272,95235566634207)]
theorem point_links_checked13865 : (cuts13865.take 3).map (fun c => (1821245441-1+2*2^9*c.k,95234272231769+c.lower,95234649561069+c.upper)) = pointBounds13865 := by
 decide +kernel
def cuts13866 : List PrefixCut := [⟨51,374598767,374599024⟩,
⟨107,800491134,800491686⟩,
⟨128,961356275,961356937⟩]
theorem checked13866 : checkPrefixCuts (2^48) 1821376513 9 Manual.Count131072.C013866.packed 128 cuts13866 = true := by
 decide +kernel
def pointBounds13866 : List (Nat × Nat × Nat) := [(1821428736,95235600992606,95235978322823),(1821486080,95236026884973,95236404215485)]
theorem point_links_checked13866 : (cuts13866.take 2).map (fun c => (1821376513-1+2*2^9*c.k,95235226393839+c.lower,95235603723799+c.upper)) = pointBounds13866 := by
 decide +kernel
def cuts13867 : List PrefixCut := [⟨35,261923286,261923471⟩,
⟨91,673727282,673727753⟩,
⟨128,953406699,953407365⟩]
theorem checked13867 : checkPrefixCuts (2^48) 1821507585 9 Manual.Count131072.C013867.packed 128 cuts13867 = true := by
 decide +kernel
def pointBounds13867 : List (Nat × Nat × Nat) := [(1821543424,95236449673400,95236827004207),(1821600768,95236861477396,95237238808489)]
theorem point_links_checked13867 : (cuts13867.take 2).map (fun c => (1821507585-1+2*2^9*c.k,95236187750114+c.lower,95236565080736+c.upper)) = pointBounds13867 := by
 decide +kernel
def cuts13868 : List PrefixCut := [⟨19,143545907,143546010⟩,
⟨75,560731961,560732348⟩,
⟨128,958282591,958283257⟩]
theorem checked13868 : checkPrefixCuts (2^48) 1821638657 9 Manual.Count131072.C013868.packed 128 cuts13868 = true := by
 decide +kernel
def pointBounds13868 : List (Nat × Nat × Nat) := [(1821658112,95237284702720,95237662034111),(1821715456,95237701888774,95238079220449)]
theorem point_links_checked13868 : (cuts13868.take 2).map (fun c => (1821638657-1+2*2^9*c.k,95237141156813+c.lower,95237518488101+c.upper)) = pointBounds13868 := by
 decide +kernel
def cuts13869 : List PrefixCut := [⟨3,23948455,23948471⟩,
⟨59,437245570,437245871⟩,
⟨115,841723210,841723795⟩,
⟨128,936583584,936584236⟩]
theorem checked13869 : checkPrefixCuts (2^48) 1821769729 9 Manual.Count131072.C013869.packed 128 cuts13869 = true := by
 decide +kernel
def pointBounds13869 : List (Nat × Nat × Nat) := [(1821772800,95238123387859,95238500719829),(1821830144,95238536684974,95238914017229),(1821887488,95238941162614,95239318495153)]
theorem point_links_checked13869 : (cuts13869.take 3).map (fun c => (1821769729-1+2*2^9*c.k,95238099439404+c.lower,95238476771358+c.upper)) = pointBounds13869 := by
 decide +kernel
def cuts13870 : List PrefixCut := [⟨43,313930359,313930578⟩,
⟨99,730432762,730433270⟩,
⟨128,953664043,953664708⟩]
theorem checked13870 : checkPrefixCuts (2^48) 1821900801 9 Manual.Count131072.C013870.packed 128 cuts13870 = true := by
 decide +kernel
def pointBounds13870 : List (Nat × Nat × Nat) := [(1821944832,95239349953347,95239727286172),(1822002176,95239766455750,95240143788864)]
theorem point_links_checked13870 : (cuts13870.take 2).map (fun c => (1821900801-1+2*2^9*c.k,95239036022988+c.lower,95239413355594+c.upper)) = pointBounds13870 := by
 decide +kernel
def cuts13871 : List PrefixCut := [⟨27,200673241,200673379⟩,
⟨83,616840511,616840935⟩,
⟨128,946181035,946181686⟩]
theorem checked13871 : checkPrefixCuts (2^48) 1822031873 9 Manual.Count131072.C013871.packed 128 cuts13871 = true := by
 decide +kernel
def pointBounds13871 : List (Nat × Nat × Nat) := [(1822059520,95240190360272,95240567693681),(1822116864,95240606527542,95240983861237)]
theorem point_links_checked13871 : (cuts13871.take 2).map (fun c => (1822031873-1+2*2^9*c.k,95239989687031+c.lower,95240367020302+c.upper)) = pointBounds13871 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000120
