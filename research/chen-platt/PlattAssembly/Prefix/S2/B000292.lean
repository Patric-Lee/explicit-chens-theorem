import PlattAssemblyKernel
import PlattCertificates.Count131072.C019344
import PlattCertificates.Count131072.C019345
import PlattCertificates.Count131072.C019346
import PlattCertificates.Count131072.C019347
import PlattCertificates.Count131072.C019348
import PlattCertificates.Count131072.C019349
import PlattCertificates.Count131072.C019350
import PlattCertificates.Count131072.C019351
import PlattCertificates.Count131072.C019352
import PlattCertificates.Count131072.C019353
import PlattCertificates.Count131072.C019354
import PlattCertificates.Count131072.C019355
import PlattCertificates.Count131072.C019356
import PlattCertificates.Count131072.C019357
import PlattCertificates.Count131072.C019358
import PlattCertificates.Count131072.C019359
import PlattCertificates.Count131072.C019360
import PlattCertificates.Count131072.C019361
import PlattCertificates.Count131072.C019362
import PlattCertificates.Count131072.C019363
import PlattCertificates.Count131072.C019364
import PlattCertificates.Count131072.C019365
import PlattCertificates.Count131072.C019366
import PlattCertificates.Count131072.C019367
import PlattCertificates.Count131072.C019368
import PlattCertificates.Count131072.C019369
import PlattCertificates.Count131072.C019370
import PlattCertificates.Count131072.C019371
import PlattCertificates.Count131072.C019372
import PlattCertificates.Count131072.C019373
import PlattCertificates.Count131072.C019374
import PlattCertificates.Count131072.C019375
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000292
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts19344 : List PrefixCut := [⟨32,161276340,161276436⟩,
⟨110,573713396,573713736⟩,
⟨128,666485001,666485396⟩]
theorem checked19344 : checkPrefixCuts (2^48) 2539388929 9 Manual.Count131072.C019344.packed 128 cuts19344 = true := by
 decide +kernel
def pointBounds19344 : List (Nat × Nat × Nat) := [(2539421696,99588477044982,99588857159115),(2539501568,99588889482038,99589269596415)]
theorem point_links_checked19344 : (cuts19344.take 2).map (fun c => (2539388929-1+2*2^9*c.k,99588315768642+c.lower,99588695882679+c.upper)) = pointBounds19344 := by
 decide +kernel
def cuts19345 : List PrefixCut := [⟨60,316770708,316770893⟩,
⟨128,668335017,668335408⟩]
theorem checked19345 : checkPrefixCuts (2^48) 2539520001 9 Manual.Count131072.C019345.packed 128 cuts19345 = true := by
 decide +kernel
def pointBounds19345 : List (Nat × Nat × Nat) := [(2539581440,99589299024351,99589679138968)]
theorem point_links_checked19345 : (cuts19345.take 1).map (fun c => (2539520001-1+2*2^9*c.k,99588982253643+c.lower,99589362368075+c.upper)) = pointBounds19345 := by
 decide +kernel
def cuts19346 : List PrefixCut := [⟨10,51980157,51980188⟩,
⟨88,461718375,461718647⟩,
⟨128,672733504,672733904⟩]
theorem checked19346 : checkPrefixCuts (2^48) 2539651073 9 Manual.Count131072.C019346.packed 128 cuts19346 = true := by
 decide +kernel
def pointBounds19346 : List (Nat × Nat × Nat) := [(2539661312,99589702568817,99590082683671),(2539741184,99590112307035,99590492422130)]
theorem point_links_checked19346 : (cuts19346.take 2).map (fun c => (2539651073-1+2*2^9*c.k,99589650588660+c.lower,99590030703483+c.upper)) = pointBounds19346 := by
 decide +kernel
def cuts19347 : List PrefixCut := [⟨38,196272048,196272163⟩,
⟨116,613963721,613964085⟩,
⟨128,674361137,674361538⟩]
theorem checked19347 : checkPrefixCuts (2^48) 2539782145 9 Manual.Count131072.C019347.packed 128 cuts19347 = true := by
 decide +kernel
def pointBounds19347 : List (Nat × Nat × Nat) := [(2539821056,99590519594212,99590899709550),(2539900928,99590937285885,99591317401472)]
theorem point_links_checked19347 : (cuts19347.take 2).map (fun c => (2539782145-1+2*2^9*c.k,99590323322164+c.lower,99590703437387+c.upper)) = pointBounds19347 := by
 decide +kernel
def cuts19348 : List PrefixCut := [⟨66,337887813,337888021⟩,
⟨128,666236617,666237019⟩]
theorem checked19348 : checkPrefixCuts (2^48) 2539913217 9 Manual.Count131072.C019348.packed 128 cuts19348 = true := by
 decide +kernel
def pointBounds19348 : List (Nat × Nat × Nat) := [(2539980800,99591335571114,99591715686946)]
theorem point_links_checked19348 : (cuts19348.take 1).map (fun c => (2539913217-1+2*2^9*c.k,99590997683301+c.lower,99591377798925+c.upper)) = pointBounds19348 := by
 decide +kernel
def cuts19349 : List PrefixCut := [⟨16,85438060,85438110⟩,
⟨94,492673923,492674216⟩,
⟨128,668861812,668862211⟩]
theorem checked19349 : checkPrefixCuts (2^48) 2540044289 9 Manual.Count131072.C019349.packed 128 cuts19349 = true := by
 decide +kernel
def pointBounds19349 : List (Nat × Nat × Nat) := [(2540060672,99591749357978,99592129474054),(2540140544,99592156593841,99592536710160)]
theorem point_links_checked19349 : (cuts19349.take 2).map (fun c => (2540044289-1+2*2^9*c.k,99591663919918+c.lower,99592044035944+c.upper)) = pointBounds19349 := by
 decide +kernel
def cuts19350 : List PrefixCut := [⟨44,229262296,229262430⟩,
⟨122,642456175,642456556⟩,
⟨128,675364862,675365261⟩]
theorem checked19350 : checkPrefixCuts (2^48) 2540175361 9 Manual.Count131072.C019350.packed 128 cuts19350 = true := by
 decide +kernel
def pointBounds19350 : List (Nat × Nat × Nat) := [(2540220416,99592562044026,99592942160585),(2540300288,99592975237905,99593355354711)]
theorem point_links_checked19350 : (cuts19350.take 2).map (fun c => (2540175361-1+2*2^9*c.k,99592332781730+c.lower,99592712898155+c.upper)) = pointBounds19350 := by
 decide +kernel
def cuts19351 : List PrefixCut := [⟨72,369967543,369967770⟩,
⟨128,666354985,666355388⟩]
theorem checked19351 : checkPrefixCuts (2^48) 2540306433 9 Manual.Count131072.C019351.packed 128 cuts19351 = true := by
 decide +kernel
def pointBounds19351 : List (Nat × Nat × Nat) := [(2540380160,99593378114135,99593758231186)]
theorem point_links_checked19351 : (cuts19351.take 1).map (fun c => (2540306433-1+2*2^9*c.k,99593008146592+c.lower,99593388263416+c.upper)) = pointBounds19351 := by
 decide +kernel
def cuts19352 : List PrefixCut := [⟨22,118885518,118885591⟩,
⟨100,523509139,523509452⟩,
⟨128,675295167,675295569⟩]
theorem checked19352 : checkPrefixCuts (2^48) 2540437505 9 Manual.Count131072.C019352.packed 128 cuts19352 = true := by
 decide +kernel
def pointBounds19352 : List (Nat × Nat × Nat) := [(2540460032,99593793387095,99594173504395),(2540539904,99594198010716,99594578128256)]
theorem point_links_checked19352 : (cuts19352.take 2).map (fun c => (2540437505-1+2*2^9*c.k,99593674501577+c.lower,99594054618804+c.upper)) = pointBounds19352 := by
 decide +kernel
def cuts19353 : List PrefixCut := [⟨50,260801962,260802116⟩,
⟨128,667394322,667394721⟩]
theorem checked19353 : checkPrefixCuts (2^48) 2540568577 9 Manual.Count131072.C019353.packed 128 cuts19353 = true := by
 decide +kernel
def pointBounds19353 : List (Nat × Nat × Nat) := [(2540619776,99594610598706,99594990716489),(2540699648,99595017191066,99595397309094)]
theorem point_links_checked19353 : (cuts19353.take 2).map (fun c => (2540568577-1+2*2^9*c.k,99594349796744+c.lower,99594729914373+c.upper)) = pointBounds19353 := by
 decide +kernel
def cuts19354 : List PrefixCut := [⟨78,405693361,405693605⟩,
⟨128,673120578,673120980⟩]
theorem checked19354 : checkPrefixCuts (2^48) 2540699649 9 Manual.Count131072.C019354.packed 128 cuts19354 = true := by
 decide +kernel
def pointBounds19354 : List (Nat × Nat × Nat) := [(2540779520,99595422884427,99595803002699)]
theorem point_links_checked19354 : (cuts19354.take 1).map (fun c => (2540699649-1+2*2^9*c.k,99595017191066+c.lower,99595397309094+c.upper)) = pointBounds19354 := by
 decide +kernel
def cuts19355 : List PrefixCut := [⟨28,143570920,143571006⟩,
⟨106,555552968,555553300⟩,
⟨128,672531827,672532227⟩]
theorem checked19355 : checkPrefixCuts (2^48) 2540830721 9 Manual.Count131072.C019355.packed 128 cuts19355 = true := by
 decide +kernel
def pointBounds19355 : List (Nat × Nat × Nat) := [(2540859392,99595833882564,99596214001080),(2540939264,99596245864612,99596625983374)]
theorem point_links_checked19355 : (cuts19355.take 2).map (fun c => (2540830721-1+2*2^9*c.k,99595690311644+c.lower,99596070430074+c.upper)) = pointBounds19355 := by
 decide +kernel
def cuts19356 : List PrefixCut := [⟨56,293993354,293993528⟩,
⟨128,671611125,671611522⟩]
theorem checked19356 : checkPrefixCuts (2^48) 2540961793 9 Manual.Count131072.C019356.packed 128 cuts19356 = true := by
 decide +kernel
def pointBounds19356 : List (Nat × Nat × Nat) := [(2541019136,99596656836825,99597036955829)]
theorem point_links_checked19356 : (cuts19356.take 1).map (fun c => (2540961793-1+2*2^9*c.k,99596362843471+c.lower,99596742962301+c.upper)) = pointBounds19356 := by
 decide +kernel
def cuts19357 : List PrefixCut := [⟨6,33563035,33563055⟩,
⟨84,445727906,445728172⟩,
⟨128,678444141,678444548⟩]
theorem checked19357 : checkPrefixCuts (2^48) 2541092865 9 Manual.Count131072.C019357.packed 128 cuts19357 = true := by
 decide +kernel
def pointBounds19357 : List (Nat × Nat × Nat) := [(2541099008,99597068017631,99597448136878),(2541178880,99597480182502,99597860301995)]
theorem point_links_checked19357 : (cuts19357.take 2).map (fun c => (2541092865-1+2*2^9*c.k,99597034454596+c.lower,99597414573823+c.upper)) = pointBounds19357 := by
 decide +kernel
def cuts19358 : List PrefixCut := [⟨34,175891260,175891366⟩,
⟨112,591020689,591021039⟩,
⟨128,674864618,674865016⟩]
theorem checked19358 : checkPrefixCuts (2^48) 2541223937 9 Manual.Count131072.C019358.packed 128 cuts19358 = true := by
 decide +kernel
def pointBounds19358 : List (Nat × Nat × Nat) := [(2541258752,99597888789997,99598268909737),(2541338624,99598303919426,99598684039410)]
theorem point_links_checked19358 : (cuts19358.take 2).map (fun c => (2541223937-1+2*2^9*c.k,99597712898737+c.lower,99598093018371+c.upper)) = pointBounds19358 := by
 decide +kernel
def cuts19359 : List PrefixCut := [⟨62,331715470,331715666⟩,
⟨128,679813864,679814273⟩]
theorem checked19359 : checkPrefixCuts (2^48) 2541355009 9 Manual.Count131072.C019359.packed 128 cuts19359 = true := by
 decide +kernel
def pointBounds19359 : List (Nat × Nat × Nat) := [(2541418496,99598719478825,99599099599053)]
theorem point_links_checked19359 : (cuts19359.take 1).map (fun c => (2541355009-1+2*2^9*c.k,99598387763355+c.lower,99598767883387+c.upper)) = pointBounds19359 := by
 decide +kernel
def cuts19360 : List PrefixCut := [⟨12,60581247,60581285⟩,
⟨90,462935284,462935564⟩,
⟨128,662501741,662502141⟩]
theorem checked19360 : checkPrefixCuts (2^48) 2541486081 9 Manual.Count131072.C019360.packed 128 cuts19360 = true := by
 decide +kernel
def pointBounds19360 : List (Nat × Nat × Nat) := [(2541498368,99599128158466,99599508278945),(2541578240,99599530512503,99599910633224)]
theorem point_links_checked19360 : (cuts19360.take 2).map (fun c => (2541486081-1+2*2^9*c.k,99599067577219+c.lower,99599447697660+c.upper)) = pointBounds19360 := by
 decide +kernel
def cuts19361 : List PrefixCut := [⟨40,205100648,205100767⟩,
⟨118,615070640,615071002⟩,
⟨128,668226263,668226657⟩]
theorem checked19361 : checkPrefixCuts (2^48) 2541617153 9 Manual.Count131072.C019361.packed 128 cuts19361 = true := by
 decide +kernel
def pointBounds19361 : List (Nat × Nat × Nat) := [(2541658112,99599935179608,99600315300568),(2541737984,99600345149600,99600725270803)]
theorem point_links_checked19361 : (cuts19361.take 2).map (fun c => (2541617153-1+2*2^9*c.k,99599730078960+c.lower,99600110199801+c.upper)) = pointBounds19361 := by
 decide +kernel
def cuts19362 : List PrefixCut := [⟨68,355583402,355583613⟩,
⟨128,668634931,668635329⟩]
theorem checked19362 : checkPrefixCuts (2^48) 2541748225 9 Manual.Count131072.C019362.packed 128 cuts19362 = true := by
 decide +kernel
def pointBounds19362 : List (Nat × Nat × Nat) := [(2541817856,99600753888625,99601134010071)]
theorem point_links_checked19362 : (cuts19362.take 1).map (fun c => (2541748225-1+2*2^9*c.k,99600398305223+c.lower,99600778426458+c.upper)) = pointBounds19362 := by
 decide +kernel
def cuts19363 : List PrefixCut := [⟨18,95120986,95121046⟩,
⟨96,503169972,503170273⟩,
⟨128,675908748,675909152⟩]
theorem checked19363 : checkPrefixCuts (2^48) 2541879297 9 Manual.Count131072.C019363.packed 128 cuts19363 = true := by
 decide +kernel
def pointBounds19363 : List (Nat × Nat × Nat) := [(2541897728,99601162061140,99601542182833),(2541977600,99601570110126,99601950232060)]
theorem point_links_checked19363 : (cuts19363.take 2).map (fun c => (2541879297-1+2*2^9*c.k,99601066940154+c.lower,99601447061787+c.upper)) = pointBounds19363 := by
 decide +kernel
def cuts19364 : List PrefixCut := [⟨46,238065681,238065825⟩,
⟨124,650518044,650518428⟩,
⟨128,672441322,672441719⟩]
theorem checked19364 : checkPrefixCuts (2^48) 2542010369 9 Manual.Count131072.C019364.packed 128 cuts19364 = true := by
 decide +kernel
def pointBounds19364 : List (Nat × Nat × Nat) := [(2542057472,99601980914583,99602361036764),(2542137344,99602393366946,99602773489367)]
theorem point_links_checked19364 : (cuts19364.take 2).map (fun c => (2542010369-1+2*2^9*c.k,99601742848902+c.lower,99602122970939+c.upper)) = pointBounds19364 := by
 decide +kernel
def cuts19365 : List PrefixCut := [⟨74,379001023,379001250⟩,
⟨128,664766838,664767233⟩]
theorem checked19365 : checkPrefixCuts (2^48) 2542141441 9 Manual.Count131072.C019365.packed 128 cuts19365 = true := by
 decide +kernel
def pointBounds19365 : List (Nat × Nat × Nat) := [(2542217216,99602794291247,99603174413908)]
theorem point_links_checked19365 : (cuts19365.take 1).map (fun c => (2542141441-1+2*2^9*c.k,99602415290224+c.lower,99602795412658+c.upper)) = pointBounds19365 := by
 decide +kernel
def cuts19366 : List PrefixCut := [⟨24,124446237,124446312⟩,
⟨102,535531167,535531483⟩,
⟨128,671597073,671597473⟩]
theorem checked19366 : checkPrefixCuts (2^48) 2542272513 9 Manual.Count131072.C019366.packed 128 cuts19366 = true := by
 decide +kernel
def pointBounds19366 : List (Nat × Nat × Nat) := [(2542297088,99603204503299,99603584626203),(2542376960,99603615588229,99603995711374)]
theorem point_links_checked19366 : (cuts19366.take 2).map (fun c => (2542272513-1+2*2^9*c.k,99603080057062+c.lower,99603460179891+c.upper)) = pointBounds19366 := by
 decide +kernel
def cuts19367 : List PrefixCut := [⟨52,272681106,272681264⟩,
⟨128,668794731,668795124⟩]
theorem checked19367 : checkPrefixCuts (2^48) 2542403585 9 Manual.Count131072.C019367.packed 128 cuts19367 = true := by
 decide +kernel
def pointBounds19367 : List (Nat × Nat × Nat) := [(2542456832,99604024335241,99604404458628)]
theorem point_links_checked19367 : (cuts19367.take 1).map (fun c => (2542403585-1+2*2^9*c.k,99603751654135+c.lower,99604131777364+c.upper)) = pointBounds19367 := by
 decide +kernel
def cuts19368 : List PrefixCut := [⟨2,10738518,10738524⟩,
⟨80,420899032,420899280⟩,
⟨128,673520497,673520893⟩]
theorem checked19368 : checkPrefixCuts (2^48) 2542534657 9 Manual.Count131072.C019368.packed 128 cuts19368 = true := by
 decide +kernel
def pointBounds19368 : List (Nat × Nat × Nat) := [(2542536704,99604431187384,99604811311012),(2542616576,99604841347898,99605221471768)]
theorem point_links_checked19368 : (cuts19368.take 2).map (fun c => (2542534657-1+2*2^9*c.k,99604420448866+c.lower,99604800572488+c.upper)) = pointBounds19368 := by
 decide +kernel
def cuts19369 : List PrefixCut := [⟨30,158411761,158411850⟩,
⟨108,562347384,562347716⟩,
⟨128,666954575,666954969⟩]
theorem checked19369 : checkPrefixCuts (2^48) 2542665729 9 Manual.Count131072.C019369.packed 128 cuts19369 = true := by
 decide +kernel
def pointBounds19369 : List (Nat × Nat × Nat) := [(2542696448,99605252381124,99605632505231),(2542776320,99605656316747,99606036441097)]
theorem point_links_checked19369 : (cuts19369.take 2).map (fun c => (2542665729-1+2*2^9*c.k,99605093969363+c.lower,99605474093381+c.upper)) = pointBounds19369 := by
 decide +kernel
def cuts19370 : List PrefixCut := [⟨58,302857941,302858125⟩,
⟨128,672011947,672012347⟩]
theorem checked19370 : checkPrefixCuts (2^48) 2542796801 9 Manual.Count131072.C019370.packed 128 cuts19370 = true := by
 decide +kernel
def pointBounds19370 : List (Nat × Nat × Nat) := [(2542856192,99606063781879,99606443906475)]
theorem point_links_checked19370 : (cuts19370.take 1).map (fun c => (2542796801-1+2*2^9*c.k,99605760923938+c.lower,99606141048350+c.upper)) = pointBounds19370 := by
 decide +kernel
def cuts19371 : List PrefixCut := [⟨8,38077055,38077080⟩,
⟨86,444299146,444299409⟩,
⟨128,664450641,664451037⟩]
theorem checked19371 : checkPrefixCuts (2^48) 2542927873 9 Manual.Count131072.C019371.packed 128 cuts19371 = true := by
 decide +kernel
def pointBounds19371 : List (Nat × Nat × Nat) := [(2542936064,99606471012940,99606851137777),(2543015936,99606877235031,99607257360106)]
theorem point_links_checked19371 : (cuts19371.take 2).map (fun c => (2542927873-1+2*2^9*c.k,99606432935885+c.lower,99606813060697+c.upper)) = pointBounds19371 := by
 decide +kernel
def cuts19372 : List PrefixCut := [⟨36,183954789,183954898⟩,
⟨114,589819245,589819600⟩,
⟨128,661649394,661649792⟩]
theorem checked19372 : checkPrefixCuts (2^48) 2543058945 9 Manual.Count131072.C019372.packed 128 cuts19372 = true := by
 decide +kernel
def pointBounds19372 : List (Nat × Nat × Nat) := [(2543095808,99607281341315,99607661466632),(2543175680,99607687205771,99608067331334)]
theorem point_links_checked19372 : (cuts19372.take 2).map (fun c => (2543058945-1+2*2^9*c.k,99607097386526+c.lower,99607477511734+c.upper)) = pointBounds19372 := by
 decide +kernel
def cuts19373 : List PrefixCut := [⟨64,331807982,331808180⟩,
⟨128,664935500,664935896⟩]
theorem checked19373 : checkPrefixCuts (2^48) 2543190017 9 Manual.Count131072.C019373.packed 128 cuts19373 = true := by
 decide +kernel
def pointBounds19373 : List (Nat × Nat × Nat) := [(2543255552,99608090843902,99608470969706)]
theorem point_links_checked19373 : (cuts19373.take 1).map (fun c => (2543190017-1+2*2^9*c.k,99607759035920+c.lower,99608139161526+c.upper)) = pointBounds19373 := by
 decide +kernel
def cuts19374 : List PrefixCut := [⟨14,76474267,76474310⟩,
⟨92,484735267,484735555⟩,
⟨128,671762981,671763381⟩]
theorem checked19374 : checkPrefixCuts (2^48) 2543321089 9 Manual.Count131072.C019374.packed 128 cuts19374 = true := by
 decide +kernel
def pointBounds19374 : List (Nat × Nat × Nat) := [(2543335424,99608500445687,99608880571732),(2543415296,99608908706687,99609288832977)]
theorem point_links_checked19374 : (cuts19374.take 2).map (fun c => (2543321089-1+2*2^9*c.k,99608423971420+c.lower,99608804097422+c.upper)) = pointBounds19374 := by
 decide +kernel
def cuts19375 : List PrefixCut := [⟨42,223212372,223212501⟩,
⟨120,633218217,633218591⟩,
⟨128,674716075,674716475⟩]
theorem checked19375 : checkPrefixCuts (2^48) 2543452161 9 Manual.Count131072.C019375.packed 128 cuts19375 = true := by
 decide +kernel
def pointBounds19375 : List (Nat × Nat × Nat) := [(2543495168,99609318946773,99609699073304),(2543575040,99609728952618,99610109079394)]
theorem point_links_checked19375 : (cuts19375.take 2).map (fun c => (2543452161-1+2*2^9*c.k,99609095734401+c.lower,99609475860803+c.upper)) = pointBounds19375 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000292
