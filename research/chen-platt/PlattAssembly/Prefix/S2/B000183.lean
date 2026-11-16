import PlattAssemblyKernel
import PlattCertificates.Count131072.C015856
import PlattCertificates.Count131072.C015857
import PlattCertificates.Count131072.C015858
import PlattCertificates.Count131072.C015859
import PlattCertificates.Count131072.C015860
import PlattCertificates.Count131072.C015861
import PlattCertificates.Count131072.C015862
import PlattCertificates.Count131072.C015863
import PlattCertificates.Count131072.C015864
import PlattCertificates.Count131072.C015865
import PlattCertificates.Count131072.C015866
import PlattCertificates.Count131072.C015867
import PlattCertificates.Count131072.C015868
import PlattCertificates.Count131072.C015869
import PlattCertificates.Count131072.C015870
import PlattCertificates.Count131072.C015871
import PlattCertificates.Count131072.C015872
import PlattCertificates.Count131072.C015873
import PlattCertificates.Count131072.C015874
import PlattCertificates.Count131072.C015875
import PlattCertificates.Count131072.C015876
import PlattCertificates.Count131072.C015877
import PlattCertificates.Count131072.C015878
import PlattCertificates.Count131072.C015879
import PlattCertificates.Count131072.C015880
import PlattCertificates.Count131072.C015881
import PlattCertificates.Count131072.C015882
import PlattCertificates.Count131072.C015883
import PlattCertificates.Count131072.C015884
import PlattCertificates.Count131072.C015885
import PlattCertificates.Count131072.C015886
import PlattCertificates.Count131072.C015887
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000183
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts15856 : List PrefixCut := [⟨38,245621308,245621469⟩,
⟨102,663721324,663721756⟩,
⟨128,833634042,833634581⟩]
theorem checked15856 : checkPrefixCuts (2^48) 2082209793 9 Manual.Count131072.C015856.packed 128 cuts15856 = true := by
 decide +kernel
def pointBounds15856 : List (Nat × Nat × Nat) := [(2082248704,96996610123168,96996988634889),(2082314240,96997028223184,96997406735176)]
theorem point_links_checked15856 : (cuts15856.take 2).map (fun c => (2082209793-1+2*2^9*c.k,96996364501860+c.lower,96996743013420+c.upper)) = pointBounds15856 := by
 decide +kernel
def cuts15857 : List PrefixCut := [⟨38,243983804,243983965⟩,
⟨102,653947377,653947806⟩,
⟨128,825741680,825742218⟩]
theorem checked15857 : checkPrefixCuts (2^48) 2082340865 9 Manual.Count131072.C015857.packed 128 cuts15857 = true := by
 decide +kernel
def pointBounds15857 : List (Nat × Nat × Nat) := [(2082379776,96997442119706,96997820631966),(2082445312,96997852083279,96998230595807)]
theorem point_links_checked15857 : (cuts15857.take 2).map (fun c => (2082340865-1+2*2^9*c.k,96997198135902+c.lower,96997576648001+c.upper)) = pointBounds15857 := by
 decide +kernel
def cuts15858 : List PrefixCut := [⟨38,240994868,240995026⟩,
⟨102,658907004,658907433⟩,
⟨128,824878817,824879353⟩]
theorem checked15858 : checkPrefixCuts (2^48) 2082471937 9 Manual.Count131072.C015858.packed 128 cuts15858 = true := by
 decide +kernel
def pointBounds15858 : List (Nat × Nat × Nat) := [(2082510848,96998264872450,96998643385245),(2082576384,96998682784586,96999061297652)]
theorem point_links_checked15858 : (cuts15858.take 2).map (fun c => (2082471937-1+2*2^9*c.k,96998023877582+c.lower,96998402390219+c.upper)) = pointBounds15858 := by
 decide +kernel
def cuts15859 : List PrefixCut := [⟨38,249359216,249359375⟩,
⟨102,656297881,656298304⟩,
⟨128,822799810,822800341⟩]
theorem checked15859 : checkPrefixCuts (2^48) 2082603009 9 Manual.Count131072.C015859.packed 128 cuts15859 = true := by
 decide +kernel
def pointBounds15859 : List (Nat × Nat × Nat) := [(2082641920,96999098115615,96999476628947),(2082707456,96999505054280,96999883567876)]
theorem point_links_checked15859 : (cuts15859.take 2).map (fun c => (2082603009-1+2*2^9*c.k,96998848756399+c.lower,96999227269572+c.upper)) = pointBounds15859 := by
 decide +kernel
def cuts15860 : List PrefixCut := [⟨38,248532697,248532857⟩,
⟨102,664094897,664095328⟩,
⟨128,832613458,832614000⟩]
theorem checked15860 : checkPrefixCuts (2^48) 2082734081 9 Manual.Count131072.C015860.packed 128 cuts15860 = true := by
 decide +kernel
def pointBounds15860 : List (Nat × Nat × Nat) := [(2082772992,96999920088906,97000298602770),(2082838528,97000335651106,97000714165241)]
theorem point_links_checked15860 : (cuts15860.take 2).map (fun c => (2082734081-1+2*2^9*c.k,96999671556209+c.lower,97000050069913+c.upper)) = pointBounds15860 := by
 decide +kernel
def cuts15861 : List PrefixCut := [⟨38,250273797,250273956⟩,
⟨102,667161172,667161600⟩,
⟨128,834993480,834994014⟩]
theorem checked15861 : checkPrefixCuts (2^48) 2082865153 9 Manual.Count131072.C015861.packed 128 cuts15861 = true := by
 decide +kernel
def pointBounds15861 : List (Nat × Nat × Nat) := [(2082904064,97000754443464,97001132957869),(2082969600,97001171330839,97001549845513)]
theorem point_links_checked15861 : (cuts15861.take 2).map (fun c => (2082865153-1+2*2^9*c.k,97000504169667+c.lower,97000882683913+c.upper)) = pointBounds15861 := by
 decide +kernel
def cuts15862 : List PrefixCut := [⟨38,242961117,242961279⟩,
⟨102,654552356,654552784⟩,
⟨128,825211642,825212180⟩]
theorem checked15862 : checkPrefixCuts (2^48) 2082996225 9 Manual.Count131072.C015862.packed 128 cuts15862 = true := by
 decide +kernel
def pointBounds15862 : List (Nat × Nat × Nat) := [(2083035136,97001582124264,97001960639206),(2083100672,97001993715503,97002372230711)]
theorem point_links_checked15862 : (cuts15862.take 2).map (fun c => (2082996225-1+2*2^9*c.k,97001339163147+c.lower,97001717677927+c.upper)) = pointBounds15862 := by
 decide +kernel
def cuts15863 : List PrefixCut := [⟨38,245377983,245378140⟩,
⟨102,667887659,667888088⟩,
⟨128,826511128,826511664⟩]
theorem checked15863 : checkPrefixCuts (2^48) 2083127297 9 Manual.Count131072.C015863.packed 128 cuts15863 = true := by
 decide +kernel
def pointBounds15863 : List (Nat × Nat × Nat) := [(2083166208,97002409752772,97002788268247),(2083231744,97002832262448,97003210778195)]
theorem point_links_checked15863 : (cuts15863.take 2).map (fun c => (2083127297-1+2*2^9*c.k,97002164374789+c.lower,97002542890107+c.upper)) = pointBounds15863 := by
 decide +kernel
def cuts15864 : List PrefixCut := [⟨38,245227464,245227621⟩,
⟨102,651092358,651092779⟩,
⟨128,818352543,818353071⟩]
theorem checked15864 : checkPrefixCuts (2^48) 2083258369 9 Manual.Count131072.C015864.packed 128 cuts15864 = true := by
 decide +kernel
def pointBounds15864 : List (Nat × Nat × Nat) := [(2083297280,97003236113381,97003614629392),(2083362816,97003641978275,97004020494550)]
theorem point_links_checked15864 : (cuts15864.take 2).map (fun c => (2083258369-1+2*2^9*c.k,97002990885917+c.lower,97003369401771+c.upper)) = pointBounds15864 := by
 decide +kernel
def cuts15865 : List PrefixCut := [⟨38,245076888,245077046⟩,
⟨102,656860681,656861102⟩,
⟨128,823164681,823165210⟩]
theorem checked15865 : checkPrefixCuts (2^48) 2083389441 9 Manual.Count131072.C015865.packed 128 cuts15865 = true := by
 decide +kernel
def pointBounds15865 : List (Nat × Nat × Nat) := [(2083428352,97004054315348,97004432831888),(2083493888,97004466099141,97004844615944)]
theorem point_links_checked15865 : (cuts15865.take 2).map (fun c => (2083389441-1+2*2^9*c.k,97003809238460+c.lower,97004187754842+c.upper)) = pointBounds15865 := by
 decide +kernel
def cuts15866 : List PrefixCut := [⟨38,245331673,245331831⟩,
⟨102,663168577,663169004⟩,
⟨128,826625239,826625770⟩]
theorem checked15866 : checkPrefixCuts (2^48) 2083520513 9 Manual.Count131072.C015866.packed 128 cuts15866 = true := by
 decide +kernel
def pointBounds15866 : List (Nat × Nat × Nat) := [(2083559424,97004877734814,97005256251883),(2083624960,97005295571718,97005674089056)]
theorem point_links_checked15866 : (cuts15866.take 2).map (fun c => (2083520513-1+2*2^9*c.k,97004632403141+c.lower,97005010920052+c.upper)) = pointBounds15866 := by
 decide +kernel
def cuts15867 : List PrefixCut := [⟨38,242749640,242749796⟩,
⟨102,657858677,657859099⟩,
⟨128,826978428,826978957⟩]
theorem checked15867 : checkPrefixCuts (2^48) 2083651585 9 Manual.Count131072.C015867.packed 128 cuts15867 = true := by
 decide +kernel
def pointBounds15867 : List (Nat × Nat × Nat) := [(2083690496,97005701778020,97006080295618),(2083756032,97006116887057,97006495404921)]
theorem point_links_checked15867 : (cuts15867.take 2).map (fun c => (2083651585-1+2*2^9*c.k,97005459028380+c.lower,97005837545822+c.upper)) = pointBounds15867 := by
 decide +kernel
def cuts15868 : List PrefixCut := [⟨38,241518623,241518780⟩,
⟨102,656601479,656601902⟩,
⟨128,822603962,822604492⟩]
theorem checked15868 : checkPrefixCuts (2^48) 2083782657 9 Manual.Count131072.C015868.packed 128 cuts15868 = true := by
 decide +kernel
def pointBounds15868 : List (Nat × Nat × Nat) := [(2083821568,97006527525431,97006906043559),(2083887104,97006942608287,97007321126681)]
theorem point_links_checked15868 : (cuts15868.take 2).map (fun c => (2083782657-1+2*2^9*c.k,97006286006808+c.lower,97006664524779+c.upper)) = pointBounds15868 := by
 decide +kernel
def cuts15869 : List PrefixCut := [⟨38,246636080,246636236⟩,
⟨102,668040945,668041372⟩,
⟨128,835383610,835384147⟩]
theorem checked15869 : checkPrefixCuts (2^48) 2083913729 9 Manual.Count131072.C015869.packed 128 cuts15869 = true := by
 decide +kernel
def pointBounds15869 : List (Nat × Nat × Nat) := [(2083952640,97007355246850,97007733765507),(2084018176,97007776651715,97008155170643)]
theorem point_links_checked15869 : (cuts15869.take 2).map (fun c => (2083913729-1+2*2^9*c.k,97007108610770+c.lower,97007487129271+c.upper)) = pointBounds15869 := by
 decide +kernel
def cuts15870 : List PrefixCut := [⟨38,250267209,250267369⟩,
⟨102,660705968,660706389⟩,
⟨128,820340010,820340535⟩]
theorem checked15870 : checkPrefixCuts (2^48) 2084044801 9 Manual.Count131072.C015870.packed 128 cuts15870 = true := by
 decide +kernel
def pointBounds15870 : List (Nat × Nat × Nat) := [(2084083712,97008194261589,97008572780787),(2084149248,97008604700348,97008983219807)]
theorem point_links_checked15870 : (cuts15870.take 2).map (fun c => (2084044801-1+2*2^9*c.k,97007943994380+c.lower,97008322513418+c.upper)) = pointBounds15870 := by
 decide +kernel
def cuts15871 : List PrefixCut := [⟨38,240932880,240933036⟩,
⟨102,656747810,656748229⟩,
⟨128,818532538,818533066⟩]
theorem checked15871 : checkPrefixCuts (2^48) 2084175873 9 Manual.Count131072.C015871.packed 128 cuts15871 = true := by
 decide +kernel
def pointBounds15871 : List (Nat × Nat × Nat) := [(2084214784,97009005267270,97009383786989),(2084280320,97009421082200,97009799602182)]
theorem point_links_checked15871 : (cuts15871.take 2).map (fun c => (2084175873-1+2*2^9*c.k,97008764334390+c.lower,97009142853953+c.upper)) = pointBounds15871 := by
 decide +kernel
def cuts15872 : List PrefixCut := [⟨38,251451112,251451273⟩,
⟨102,663998932,663999365⟩,
⟨128,828474223,828474766⟩]
theorem checked15872 : checkPrefixCuts (2^48) 2084306945 9 Manual.Count131072.C015872.packed 128 cuts15872 = true := by
 decide +kernel
def pointBounds15872 : List (Nat × Nat × Nat) := [(2084345856,97009834318040,97010212838292),(2084411392,97010246865860,97010625386384)]
theorem point_links_checked15872 : (cuts15872.take 2).map (fun c => (2084306945-1+2*2^9*c.k,97009582866928+c.lower,97009961387019+c.upper)) = pointBounds15872 := by
 decide +kernel
def cuts15873 : List PrefixCut := [⟨38,240632545,240632699⟩,
⟨102,649913570,649913989⟩,
⟨128,812353116,812353637⟩]
theorem checked15873 : checkPrefixCuts (2^48) 2084438017 9 Manual.Count131072.C015873.packed 128 cuts15873 = true := by
 decide +kernel
def pointBounds15873 : List (Nat × Nat × Nat) := [(2084476928,97010651973696,97011030494484),(2084542464,97011061254721,97011439775774)]
theorem point_links_checked15873 : (cuts15873.take 2).map (fun c => (2084438017-1+2*2^9*c.k,97010411341151+c.lower,97010789861785+c.upper)) = pointBounds15873 := by
 decide +kernel
def cuts15874 : List PrefixCut := [⟨38,238592008,238592164⟩,
⟨102,653923333,653923752⟩,
⟨128,817837889,817838414⟩]
theorem checked15874 : checkPrefixCuts (2^48) 2084569089 9 Manual.Count131072.C015874.packed 128 cuts15874 = true := by
 decide +kernel
def pointBounds15874 : List (Nat × Nat × Nat) := [(2084608000,97011462286275,97011840807586),(2084673536,97011877617600,97012256139174)]
theorem point_links_checked15874 : (cuts15874.take 2).map (fun c => (2084569089-1+2*2^9*c.k,97011223694267+c.lower,97011602215422+c.upper)) = pointBounds15874 := by
 decide +kernel
def cuts15875 : List PrefixCut := [⟨38,239387120,239387276⟩,
⟨102,647806686,647807102⟩,
⟨128,820351680,820352210⟩]
theorem checked15875 : checkPrefixCuts (2^48) 2084700161 9 Manual.Count131072.C015875.packed 128 cuts15875 = true := by
 decide +kernel
def pointBounds15875 : List (Nat × Nat × Nat) := [(2084739072,97012280919276,97012659441112),(2084804608,97012689338842,97013067860938)]
theorem point_links_checked15875 : (cuts15875.take 2).map (fun c => (2084700161-1+2*2^9*c.k,97012041532156+c.lower,97012420053836+c.upper)) = pointBounds15875 := by
 decide +kernel
def cuts15876 : List PrefixCut := [⟨38,247337566,247337727⟩,
⟨102,663831899,663832333⟩,
⟨128,832585962,832586502⟩]
theorem checked15876 : checkPrefixCuts (2^48) 2084831233 9 Manual.Count131072.C015876.packed 128 cuts15876 = true := by
 decide +kernel
def pointBounds15876 : List (Nat × Nat × Nat) := [(2084870144,97013109221402,97013487743773),(2084935680,97013525715735,97013904238379)]
theorem point_links_checked15876 : (cuts15876.take 2).map (fun c => (2084831233-1+2*2^9*c.k,97012861883836+c.lower,97013240406046+c.upper)) = pointBounds15876 := by
 decide +kernel
def cuts15877 : List PrefixCut := [⟨38,247862025,247862185⟩,
⟨102,657040199,657040625⟩,
⟨128,824433728,824434258⟩]
theorem checked15877 : checkPrefixCuts (2^48) 2084962305 9 Manual.Count131072.C015877.packed 128 cuts15877 = true := by
 decide +kernel
def pointBounds15877 : List (Nat × Nat × Nat) := [(2085001216,97013942331823,97014320854733),(2085066752,97014351509997,97014730033173)]
theorem point_links_checked15877 : (cuts15877.take 2).map (fun c => (2084962305-1+2*2^9*c.k,97013694469798+c.lower,97014072992548+c.upper)) = pointBounds15877 := by
 decide +kernel
def cuts15878 : List PrefixCut := [⟨38,257160997,257161164⟩,
⟨102,668473279,668473714⟩,
⟨128,836666179,836666726⟩]
theorem checked15878 : checkPrefixCuts (2^48) 2085093377 9 Manual.Count131072.C015878.packed 128 cuts15878 = true := by
 decide +kernel
def pointBounds15878 : List (Nat × Nat × Nat) := [(2085132288,97014776064523,97015154587970),(2085197824,97015187376805,97015565900520)]
theorem point_links_checked15878 : (cuts15878.take 2).map (fun c => (2085093377-1+2*2^9*c.k,97014518903526+c.lower,97014897426806+c.upper)) = pointBounds15878 := by
 decide +kernel
def cuts15879 : List PrefixCut := [⟨38,246346077,246346235⟩,
⟨102,648993824,648994241⟩,
⟨128,821765385,821765915⟩]
theorem checked15879 : checkPrefixCuts (2^48) 2085224449 9 Manual.Count131072.C015879.packed 128 cuts15879 = true := by
 decide +kernel
def pointBounds15879 : List (Nat × Nat × Nat) := [(2085263360,97015601915782,97015980439767),(2085328896,97016004563529,97016383087773)]
theorem point_links_checked15879 : (cuts15879.take 2).map (fun c => (2085224449-1+2*2^9*c.k,97015355569705+c.lower,97015734093532+c.upper)) = pointBounds15879 := by
 decide +kernel
def cuts15880 : List PrefixCut := [⟨38,246060613,246060767⟩,
⟨102,656781206,656781623⟩,
⟨128,823333318,823333840⟩]
theorem checked15880 : checkPrefixCuts (2^48) 2085355521 9 Manual.Count131072.C015880.packed 128 cuts15880 = true := by
 decide +kernel
def pointBounds15880 : List (Nat × Nat × Nat) := [(2085394432,97016423395703,97016801920214),(2085459968,97016834116296,97017212641070)]
theorem point_links_checked15880 : (cuts15880.take 2).map (fun c => (2085355521-1+2*2^9*c.k,97016177335090+c.lower,97016555859447+c.upper)) = pointBounds15880 := by
 decide +kernel
def cuts15881 : List PrefixCut := [⟨38,243750726,243750883⟩,
⟨102,654040695,654041120⟩,
⟨128,819637590,819638124⟩]
theorem checked15881 : checkPrefixCuts (2^48) 2085486593 9 Manual.Count131072.C015881.packed 128 cuts15881 = true := by
 decide +kernel
def pointBounds15881 : List (Nat × Nat × Nat) := [(2085525504,97017244419134,97017622944170),(2085591040,97017654709103,97018033234407)]
theorem point_links_checked15881 : (cuts15881.take 2).map (fun c => (2085486593-1+2*2^9*c.k,97017000668408+c.lower,97017379193287+c.upper)) = pointBounds15881 := by
 decide +kernel
def cuts15882 : List PrefixCut := [⟨38,243600448,243600606⟩,
⟨102,655349103,655349527⟩,
⟨128,824039529,824040059⟩]
theorem checked15882 : checkPrefixCuts (2^48) 2085617665 9 Manual.Count131072.C015882.packed 128 cuts15882 = true := by
 decide +kernel
def pointBounds15882 : List (Nat × Nat × Nat) := [(2085656576,97018063906446,97018442432017),(2085722112,97018475655101,97018854180938)]
theorem point_links_checked15882 : (cuts15882.take 2).map (fun c => (2085617665-1+2*2^9*c.k,97017820305998+c.lower,97018198831411+c.upper)) = pointBounds15882 := by
 decide +kernel
def cuts15883 : List PrefixCut := [⟨38,243585134,243585290⟩,
⟨102,653553583,653554005⟩,
⟨128,816700729,816701258⟩]
theorem checked15883 : checkPrefixCuts (2^48) 2085748737 9 Manual.Count131072.C015883.packed 128 cuts15883 = true := by
 decide +kernel
def pointBounds15883 : List (Nat × Nat × Nat) := [(2085787648,97018887930661,97019266456760),(2085853184,97019297899110,97019676425475)]
theorem point_links_checked15883 : (cuts15883.take 2).map (fun c => (2085748737-1+2*2^9*c.k,97018644345527+c.lower,97019022871470+c.upper)) = pointBounds15883 := by
 decide +kernel
def cuts15884 : List PrefixCut := [⟨38,244919296,244919452⟩,
⟨102,659719845,659720267⟩,
⟨128,822856711,822857238⟩]
theorem checked15884 : checkPrefixCuts (2^48) 2085879809 9 Manual.Count131072.C015884.packed 128 cuts15884 = true := by
 decide +kernel
def pointBounds15884 : List (Nat × Nat × Nat) := [(2085918720,97019705965552,97020084492180),(2085984256,97020120766101,97020499292995)]
theorem point_links_checked15884 : (cuts15884.take 2).map (fun c => (2085879809-1+2*2^9*c.k,97019461046256+c.lower,97019839572728+c.upper)) = pointBounds15884 := by
 decide +kernel
def cuts15885 : List PrefixCut := [⟨38,246792958,246793121⟩,
⟨102,663051687,663052119⟩,
⟨128,824019498,824020037⟩]
theorem checked15885 : checkPrefixCuts (2^48) 2086010881 9 Manual.Count131072.C015885.packed 128 cuts15885 = true := by
 decide +kernel
def pointBounds15885 : List (Nat × Nat × Nat) := [(2086049792,97020530695925,97020909223087),(2086115328,97020946954654,97021325482085)]
theorem point_links_checked15885 : (cuts15885.take 2).map (fun c => (2086010881-1+2*2^9*c.k,97020283902967+c.lower,97020662429966+c.upper)) = pointBounds15885 := by
 decide +kernel
def cuts15886 : List PrefixCut := [⟨38,245428198,245428358⟩,
⟨102,653430516,653430941⟩,
⟨128,821943639,821944172⟩]
theorem checked15886 : checkPrefixCuts (2^48) 2086141953 9 Manual.Count131072.C015886.packed 128 cuts15886 = true := by
 decide +kernel
def pointBounds15886 : List (Nat × Nat × Nat) := [(2086180864,97021353350663,97021731878361),(2086246400,97021761352981,97022139880944)]
theorem point_links_checked15886 : (cuts15886.take 2).map (fun c => (2086141953-1+2*2^9*c.k,97021107922465+c.lower,97021486450003+c.upper)) = pointBounds15886 := by
 decide +kernel
def cuts15887 : List PrefixCut := [⟨38,240016121,240016275⟩,
⟨102,650556180,650556600⟩,
⟨128,814876500,814877029⟩]
theorem checked15887 : checkPrefixCuts (2^48) 2086273025 9 Manual.Count131072.C015887.packed 128 cuts15887 = true := by
 decide +kernel
def pointBounds15887 : List (Nat × Nat × Nat) := [(2086311936,97022169882225,97022548410450),(2086377472,97022580422284,97022958950775)]
theorem point_links_checked15887 : (cuts15887.take 2).map (fun c => (2086273025-1+2*2^9*c.k,97021929866104+c.lower,97022308394175+c.upper)) = pointBounds15887 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000183
