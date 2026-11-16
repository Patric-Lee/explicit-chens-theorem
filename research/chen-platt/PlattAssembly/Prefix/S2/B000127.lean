import PlattAssemblyKernel
import PlattCertificates.Count131072.C014064
import PlattCertificates.Count131072.C014065
import PlattCertificates.Count131072.C014066
import PlattCertificates.Count131072.C014067
import PlattCertificates.Count131072.C014068
import PlattCertificates.Count131072.C014069
import PlattCertificates.Count131072.C014070
import PlattCertificates.Count131072.C014071
import PlattCertificates.Count131072.C014072
import PlattCertificates.Count131072.C014073
import PlattCertificates.Count131072.C014074
import PlattCertificates.Count131072.C014075
import PlattCertificates.Count131072.C014076
import PlattCertificates.Count131072.C014077
import PlattCertificates.Count131072.C014078
import PlattCertificates.Count131072.C014079
import PlattCertificates.Count131072.C014080
import PlattCertificates.Count131072.C014081
import PlattCertificates.Count131072.C014082
import PlattCertificates.Count131072.C014083
import PlattCertificates.Count131072.C014084
import PlattCertificates.Count131072.C014085
import PlattCertificates.Count131072.C014086
import PlattCertificates.Count131072.C014087
import PlattCertificates.Count131072.C014088
import PlattCertificates.Count131072.C014089
import PlattCertificates.Count131072.C014090
import PlattCertificates.Count131072.C014091
import PlattCertificates.Count131072.C014092
import PlattCertificates.Count131072.C014093
import PlattCertificates.Count131072.C014094
import PlattCertificates.Count131072.C014095
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000127
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts14064 : List PrefixCut := [⟨5,35501833,35501857⟩,
⟨62,455117152,455117464⟩,
⟨119,870605444,870606046⟩,
⟨128,936424169,936424817⟩]
theorem checked14064 : checkPrefixCuts (2^48) 1847328769 9 Manual.Count131072.C014064.packed 128 cuts14064 = true := by
 decide +kernel
def pointBounds14064 : List (Nat × Nat × Nat) := [(1847333888,95421970722601,95422348182268),(1847392256,95422390337920,95422767797875),(1847450624,95422805826212,95423183286457)]
theorem point_links_checked14064 : (cuts14064.take 3).map (fun c => (1847328769-1+2*2^9*c.k,95421935220768+c.lower,95422312680411+c.upper)) = pointBounds14064 := by
 decide +kernel
def cuts14065 : List PrefixCut := [⟨48,351789491,351789736⟩,
⟨105,762223967,762224501⟩,
⟨128,930263735,930264388⟩]
theorem checked14065 : checkPrefixCuts (2^48) 1847459841 9 Manual.Count131072.C014065.packed 128 cuts14065 = true := by
 decide +kernel
def pointBounds14065 : List (Nat × Nat × Nat) := [(1847508992,95423223434428,95423600894964),(1847567360,95423633868904,95424011329729)]
theorem point_links_checked14065 : (cuts14065.take 2).map (fun c => (1847459841-1+2*2^9*c.k,95422871644937+c.lower,95423249105228+c.upper)) = pointBounds14065 := by
 decide +kernel
def cuts14066 : List PrefixCut := [⟨34,249389636,249389811⟩,
⟨91,669395673,669396140⟩,
⟨128,934006291,934006944⟩]
theorem checked14066 : checkPrefixCuts (2^48) 1847590913 9 Manual.Count131072.C014066.packed 128 cuts14066 = true := by
 decide +kernel
def pointBounds14066 : List (Nat × Nat × Nat) := [(1847625728,95424051298308,95424428759427),(1847684096,95424471304345,95424848765756)]
theorem point_links_checked14066 : (cuts14066.take 2).map (fun c => (1847590913-1+2*2^9*c.k,95423801908672+c.lower,95424179369616+c.upper)) = pointBounds14066 := by
 decide +kernel
def cuts14067 : List PrefixCut := [⟨20,143195213,143195310⟩,
⟨77,557233795,557234183⟩,
⟨128,930283869,930284516⟩]
theorem checked14067 : checkPrefixCuts (2^48) 1847721985 9 Manual.Count131072.C014067.packed 128 cuts14067 = true := by
 decide +kernel
def pointBounds14067 : List (Nat × Nat × Nat) := [(1847742464,95424879110176,95425256571870),(1847800832,95425293148758,95425670610743)]
theorem point_links_checked14067 : (cuts14067.take 2).map (fun c => (1847721985-1+2*2^9*c.k,95424735914963+c.lower,95425113376560+c.upper)) = pointBounds14067 := by
 decide +kernel
def cuts14068 : List PrefixCut := [⟨6,43108004,43108034⟩,
⟨63,457881973,457882284⟩,
⟨120,875841628,875842226⟩,
⟨128,940118515,940119159⟩]
theorem checked14068 : checkPrefixCuts (2^48) 1847853057 9 Manual.Count131072.C014068.packed 128 cuts14068 = true := by
 decide +kernel
def pointBounds14068 : List (Nat × Nat × Nat) := [(1847859200,95425709306836,95426086769110),(1847917568,95426124080805,95426501543360),(1847975936,95426542040460,95426919503302)]
theorem point_links_checked14068 : (cuts14068.take 3).map (fun c => (1847853057-1+2*2^9*c.k,95425666198832+c.lower,95426043661076+c.upper)) = pointBounds14068 := by
 decide +kernel
def cuts14069 : List PrefixCut := [⟨49,360675943,360676188⟩,
⟨106,783635306,783635842⟩,
⟨128,944469062,944469707⟩]
theorem checked14069 : checkPrefixCuts (2^48) 1847984129 9 Manual.Count131072.C014069.packed 128 cuts14069 = true := by
 decide +kernel
def pointBounds14069 : List (Nat × Nat × Nat) := [(1848034304,95426966993290,95427344456423),(1848092672,95427389952653,95427767416077)]
theorem point_links_checked14069 : (cuts14069.take 2).map (fun c => (1847984129-1+2*2^9*c.k,95426606317347+c.lower,95426983780235+c.upper)) = pointBounds14069 := by
 decide +kernel
def cuts14070 : List PrefixCut := [⟨35,252517140,252517317⟩,
⟨92,674078965,674079434⟩,
⟨128,932674950,932675596⟩]
theorem checked14070 : checkPrefixCuts (2^48) 1848115201 9 Manual.Count131072.C014070.packed 128 cuts14070 = true := by
 decide +kernel
def pointBounds14070 : List (Nat × Nat × Nat) := [(1848151040,95427803303549,95428180767259),(1848209408,95428224865374,95428602329376)]
theorem point_links_checked14070 : (cuts14070.take 2).map (fun c => (1848115201-1+2*2^9*c.k,95427550786409+c.lower,95427928249942+c.upper)) = pointBounds14070 := by
 decide +kernel
def cuts14071 : List PrefixCut := [⟨21,153967285,153967394⟩,
⟨78,562405758,562406147⟩,
⟨128,929563102,929563737⟩]
theorem checked14071 : checkPrefixCuts (2^48) 1848246273 9 Manual.Count131072.C014071.packed 128 cuts14071 = true := by
 decide +kernel
def pointBounds14071 : List (Nat × Nat × Nat) := [(1848267776,95428637428644,95429014892932),(1848326144,95429045867117,95429423331685)]
theorem point_links_checked14071 : (cuts14071.take 2).map (fun c => (1848246273-1+2*2^9*c.k,95428483461359+c.lower,95428860925538+c.upper)) = pointBounds14071 := by
 decide +kernel
def cuts14072 : List PrefixCut := [⟨7,48577914,48577948⟩,
⟨64,468716104,468716426⟩,
⟨121,887165960,887166581⟩,
⟨128,936806521,936807177⟩]
theorem checked14072 : checkPrefixCuts (2^48) 1848377345 9 Manual.Count131072.C014072.packed 128 cuts14072 = true := by
 decide +kernel
def pointBounds14072 : List (Nat × Nat × Nat) := [(1848384512,95429461602375,95429839067223),(1848442880,95429881740565,95430259205701),(1848501248,95430300190421,95430677655856)]
theorem point_links_checked14072 : (cuts14072.take 3).map (fun c => (1848377345-1+2*2^9*c.k,95429413024461+c.lower,95429790489275+c.upper)) = pointBounds14072 := by
 decide +kernel
def cuts14073 : List PrefixCut := [⟨50,365293887,365294135⟩,
⟨107,781128899,781129430⟩,
⟨128,937349134,937349773⟩]
theorem checked14073 : checkPrefixCuts (2^48) 1848508417 9 Manual.Count131072.C014073.packed 128 cuts14073 = true := by
 decide +kernel
def pointBounds14073 : List (Nat × Nat × Nat) := [(1848559616,95430715124869,95431092590587),(1848617984,95431130959881,95431508425882)]
theorem point_links_checked14073 : (cuts14073.take 2).map (fun c => (1848508417-1+2*2^9*c.k,95430349830982+c.lower,95430727296452+c.upper)) = pointBounds14073 := by
 decide +kernel
def cuts14074 : List PrefixCut := [⟨36,263560392,263560576⟩,
⟨93,676476246,676476715⟩,
⟨128,926016021,926016663⟩]
theorem checked14074 : checkPrefixCuts (2^48) 1848639489 9 Manual.Count131072.C014074.packed 128 cuts14074 = true := by
 decide +kernel
def pointBounds14074 : List (Nat × Nat × Nat) := [(1848676352,95431550740508,95431928206801),(1848734720,95431963656362,95432341122940)]
theorem point_links_checked14074 : (cuts14074.take 2).map (fun c => (1848639489-1+2*2^9*c.k,95431287180116+c.lower,95431664646225+c.upper)) = pointBounds14074 := by
 decide +kernel
def cuts14075 : List PrefixCut := [⟨22,160165754,160165863⟩,
⟨79,577166285,577166682⟩,
⟨128,926102730,926103366⟩]
theorem checked14075 : checkPrefixCuts (2^48) 1848770561 9 Manual.Count131072.C014075.packed 128 cuts14075 = true := by
 decide +kernel
def pointBounds14075 : List (Nat × Nat × Nat) := [(1848793088,95432373361891,95432750828751),(1848851456,95432790362422,95433167829570)]
theorem point_links_checked14075 : (cuts14075.take 2).map (fun c => (1848770561-1+2*2^9*c.k,95432213196137+c.lower,95432590662888+c.upper)) = pointBounds14075 := by
 decide +kernel
def cuts14076 : List PrefixCut := [⟨8,57393962,57394003⟩,
⟨65,468278615,468278944⟩,
⟨122,882194828,882195450⟩,
⟨128,922383129,922383780⟩]
theorem checked14076 : checkPrefixCuts (2^48) 1848901633 9 Manual.Count131072.C014076.packed 128 cuts14076 = true := by
 decide +kernel
def pointBounds14076 : List (Nat × Nat × Nat) := [(1848909824,95433196692829,95433574160257),(1848968192,95433607577482,95433985045198),(1849026560,95434021493695,95434398961704)]
theorem point_links_checked14076 : (cuts14076.take 3).map (fun c => (1848901633-1+2*2^9*c.k,95433139298867+c.lower,95433516766254+c.upper)) = pointBounds14076 := by
 decide +kernel
def cuts14077 : List PrefixCut := [⟨51,368387039,368387290⟩,
⟨108,792476109,792476649⟩,
⟨128,941193340,941193979⟩]
theorem checked14077 : checkPrefixCuts (2^48) 1849032705 9 Manual.Count131072.C014077.packed 128 cuts14077 = true := by
 decide +kernel
def pointBounds14077 : List (Nat × Nat × Nat) := [(1849084928,95434430069035,95434807537324),(1849143296,95434854158105,95435231626683)]
theorem point_links_checked14077 : (cuts14077.take 2).map (fun c => (1849032705-1+2*2^9*c.k,95434061681996+c.lower,95434439150034+c.upper)) = pointBounds14077 := by
 decide +kernel
def cuts14078 : List PrefixCut := [⟨37,277641630,277641820⟩,
⟨94,694549869,694550344⟩,
⟨128,945388705,945389351⟩]
theorem checked14078 : checkPrefixCuts (2^48) 1849163777 9 Manual.Count131072.C014078.packed 128 cuts14078 = true := by
 decide +kernel
def pointBounds14078 : List (Nat × Nat × Nat) := [(1849201664,95435280516966,95435657985833),(1849260032,95435697425205,95436074894357)]
theorem point_links_checked14078 : (cuts14078.take 2).map (fun c => (1849163777-1+2*2^9*c.k,95435002875336+c.lower,95435380344013+c.upper)) = pointBounds14078 := by
 decide +kernel
def cuts14079 : List PrefixCut := [⟨23,168948233,168948352⟩,
⟨80,588874217,588874621⟩,
⟨128,933754500,933755142⟩]
theorem checked14079 : checkPrefixCuts (2^48) 1849294849 9 Manual.Count131072.C014079.packed 128 cuts14079 = true := by
 decide +kernel
def pointBounds14079 : List (Nat × Nat × Nat) := [(1849318400,95436117212274,95436494681716),(1849376768,95436537138258,95436914607985)]
theorem point_links_checked14079 : (cuts14079.take 2).map (fun c => (1849294849-1+2*2^9*c.k,95435948264041+c.lower,95436325733364+c.upper)) = pointBounds14079 := by
 decide +kernel
def cuts14080 : List PrefixCut := [⟨9,67574766,67574813⟩,
⟨66,479408141,479408475⟩,
⟨123,889402202,889402821⟩,
⟨128,923948253,923948895⟩]
theorem checked14080 : checkPrefixCuts (2^48) 1849425921 9 Manual.Count131072.C014080.packed 128 cuts14080 = true := by
 decide +kernel
def pointBounds14080 : List (Nat × Nat × Nat) := [(1849435136,95436949593307,95437327063319),(1849493504,95437361426682,95437738896981),(1849551872,95437771420743,95438148891327)]
theorem point_links_checked14080 : (cuts14080.take 3).map (fun c => (1849425921-1+2*2^9*c.k,95436882018541+c.lower,95437259488506+c.upper)) = pointBounds14080 := by
 decide +kernel
def cuts14081 : List PrefixCut := [⟨52,373304500,373304760⟩,
⟨109,791033743,791034292⟩,
⟨128,927991266,927991913⟩]
theorem checked14081 : checkPrefixCuts (2^48) 1849556993 9 Manual.Count131072.C014081.packed 128 cuts14081 = true := by
 decide +kernel
def pointBounds14081 : List (Nat × Nat × Nat) := [(1849610240,95438179271294,95438556742161),(1849668608,95438597000537,95438974471693)]
theorem point_links_checked14081 : (cuts14081.take 2).map (fun c => (1849556993-1+2*2^9*c.k,95437805966794+c.lower,95438183437401+c.upper)) = pointBounds14081 := by
 decide +kernel
def cuts14082 : List PrefixCut := [⟨38,276954222,276954409⟩,
⟨95,696178819,696179296⟩,
⟨128,942381528,942382175⟩]
theorem checked14082 : checkPrefixCuts (2^48) 1849688065 9 Manual.Count131072.C014082.packed 128 cuts14082 = true := by
 decide +kernel
def pointBounds14082 : List (Nat × Nat × Nat) := [(1849726976,95439010912282,95439388383723),(1849785344,95439430136879,95439807608610)]
theorem point_links_checked14082 : (cuts14082.take 2).map (fun c => (1849688065-1+2*2^9*c.k,95438733958060+c.lower,95439111429314+c.upper)) = pointBounds14082 := by
 decide +kernel
def cuts14083 : List PrefixCut := [⟨24,174682486,174682608⟩,
⟨81,586120485,586120893⟩,
⟨128,931815892,931816542⟩]
theorem checked14083 : checkPrefixCuts (2^48) 1849819137 9 Manual.Count131072.C014083.packed 128 cuts14083 = true := by
 decide +kernel
def pointBounds14083 : List (Nat × Nat × Nat) := [(1849843712,95439851022074,95440228494097),(1849902080,95440262460073,95440639932382)]
theorem point_links_checked14083 : (cuts14083.take 2).map (fun c => (1849819137-1+2*2^9*c.k,95439676339588+c.lower,95440053811489+c.upper)) = pointBounds14083 := by
 decide +kernel
def cuts14084 : List PrefixCut := [⟨10,69990041,69990091⟩,
⟨67,482923648,482923983⟩,
⟨124,890975601,890976221⟩,
⟨128,920186878,920187519⟩]
theorem checked14084 : checkPrefixCuts (2^48) 1849950209 9 Manual.Count131072.C014084.packed 128 cuts14084 = true := by
 decide +kernel
def pointBounds14084 : List (Nat × Nat × Nat) := [(1849960448,95440678145521,95441055618122),(1850018816,95441091079128,95441468552014),(1850077184,95441499131081,95441876604252)]
theorem point_links_checked14084 : (cuts14084.take 3).map (fun c => (1849950209-1+2*2^9*c.k,95440608155480+c.lower,95440985628031+c.upper)) = pointBounds14084 := by
 decide +kernel
def cuts14085 : List PrefixCut := [⟨53,391759630,391759896⟩,
⟨110,803437012,803437561⟩,
⟨128,939138653,939139294⟩]
theorem checked14085 : checkPrefixCuts (2^48) 1850081281 9 Manual.Count131072.C014085.packed 128 cuts14085 = true := by
 decide +kernel
def pointBounds14085 : List (Nat × Nat × Nat) := [(1850135552,95441920101988,95442297575446),(1850193920,95442331779370,95442709253111)]
theorem point_links_checked14085 : (cuts14085.take 2).map (fun c => (1850081281-1+2*2^9*c.k,95441528342358+c.lower,95441905815550+c.upper)) = pointBounds14085 := by
 decide +kernel
def cuts14086 : List PrefixCut := [⟨39,280070393,280070585⟩,
⟨96,694612234,694612715⟩,
⟨128,925228708,925229353⟩]
theorem checked14086 : checkPrefixCuts (2^48) 1850212353 9 Manual.Count131072.C014086.packed 128 cuts14086 = true := by
 decide +kernel
def pointBounds14086 : List (Nat × Nat × Nat) := [(1850252288,95442747551404,95443125025429),(1850310656,95443162093245,95443539567559)]
theorem point_links_checked14086 : (cuts14086.take 2).map (fun c => (1850212353-1+2*2^9*c.k,95442467481011+c.lower,95442844954844+c.upper)) = pointBounds14086 := by
 decide +kernel
def cuts14087 : List PrefixCut := [⟨25,182391050,182391174⟩,
⟨82,602078686,602079100⟩,
⟨128,931247988,931248630⟩]
theorem checked14087 : checkPrefixCuts (2^48) 1850343425 9 Manual.Count131072.C014087.packed 128 cuts14087 = true := by
 decide +kernel
def pointBounds14087 : List (Nat × Nat × Nat) := [(1850369024,95443575100769,95443952575371),(1850427392,95443994788405,95444372263297)]
theorem point_links_checked14087 : (cuts14087.take 2).map (fun c => (1850343425-1+2*2^9*c.k,95443392709719+c.lower,95443770184197+c.upper)) = pointBounds14087 := by
 decide +kernel
def cuts14088 : List PrefixCut := [⟨11,81074155,81074211⟩,
⟨68,504690134,504690479⟩,
⟨125,924033921,924034559⟩,
⟨128,946088263,946088917⟩]
theorem checked14088 : checkPrefixCuts (2^48) 1850474497 9 Manual.Count131072.C014088.packed 128 cuts14088 = true := by
 decide +kernel
def pointBounds14088 : List (Nat × Nat × Nat) := [(1850485760,95444405031862,95444782507038),(1850544128,95444828647841,95445206123306),(1850602496,95445247991628,95445625467386)]
theorem point_links_checked14088 : (cuts14088.take 3).map (fun c => (1850474497-1+2*2^9*c.k,95444323957707+c.lower,95444701432827+c.upper)) = pointBounds14088 := by
 decide +kernel
def cuts14089 : List PrefixCut := [⟨54,386933594,386933863⟩,
⟨111,810813618,810814183⟩,
⟨128,934613856,934614505⟩]
theorem checked14089 : checkPrefixCuts (2^48) 1850605569 9 Manual.Count131072.C014089.packed 128 cuts14089 = true := by
 decide +kernel
def pointBounds14089 : List (Nat × Nat × Nat) := [(1850660864,95445656979564,95446034455607),(1850719232,95446080859588,95446458335927)]
theorem point_links_checked14089 : (cuts14089.take 2).map (fun c => (1850605569-1+2*2^9*c.k,95445270045970+c.lower,95445647521744+c.upper)) = pointBounds14089 := by
 decide +kernel
def cuts14090 : List PrefixCut := [⟨40,281511795,281511992⟩,
⟨97,705365033,705365522⟩,
⟨128,935459932,935460578⟩]
theorem checked14090 : checkPrefixCuts (2^48) 1850736641 9 Manual.Count131072.C014090.packed 128 cuts14090 = true := by
 decide +kernel
def pointBounds14090 : List (Nat × Nat × Nat) := [(1850777600,95446486171621,95446863648241),(1850835968,95446910024859,95447287501771)]
theorem point_links_checked14090 : (cuts14090.take 2).map (fun c => (1850736641-1+2*2^9*c.k,95446204659826+c.lower,95446582136249+c.upper)) = pointBounds14090 := by
 decide +kernel
def cuts14091 : List PrefixCut := [⟨26,188574436,188574564⟩,
⟨83,598714433,598714847⟩,
⟨128,930375602,930376246⟩]
theorem checked14091 : checkPrefixCuts (2^48) 1850867713 9 Manual.Count131072.C014091.packed 128 cuts14091 = true := by
 decide +kernel
def pointBounds14091 : List (Nat × Nat × Nat) := [(1850894336,95447328694194,95447706171391),(1850952704,95447738834191,95448116311674)]
theorem point_links_checked14091 : (cuts14091.take 2).map (fun c => (1850867713-1+2*2^9*c.k,95447140119758+c.lower,95447517596827+c.upper)) = pointBounds14091 := by
 decide +kernel
def cuts14092 : List PrefixCut := [⟨12,87742061,87742125⟩,
⟨69,506979893,506980247⟩,
⟨126,924379868,924380506⟩,
⟨128,940801895,940802545⟩]
theorem checked14092 : checkPrefixCuts (2^48) 1850998785 9 Manual.Count131072.C014092.packed 128 cuts14092 = true := by
 decide +kernel
def pointBounds14092 : List (Nat × Nat × Nat) := [(1851011072,95448158237421,95448535715198),(1851069440,95448577475253,95448954953320),(1851127808,95448994875228,95449372353579)]
theorem point_links_checked14092 : (cuts14092.take 3).map (fun c => (1850998785-1+2*2^9*c.k,95448070495360+c.lower,95448447973073+c.upper)) = pointBounds14092 := by
 decide +kernel
def cuts14093 : List PrefixCut := [⟨55,392753999,392754269⟩,
⟨112,807846961,807847520⟩,
⟨128,923401634,923402272⟩]
theorem checked14093 : checkPrefixCuts (2^48) 1851129857 9 Manual.Count131072.C014093.packed 128 cuts14093 = true := by
 decide +kernel
def pointBounds14093 : List (Nat × Nat × Nat) := [(1851186176,95449404051254,95449781529887),(1851244544,95449819144216,95450196623138)]
theorem point_links_checked14093 : (cuts14093.take 2).map (fun c => (1851129857-1+2*2^9*c.k,95449011297255+c.lower,95449388775618+c.upper)) = pointBounds14093 := by
 decide +kernel
def cuts14094 : List PrefixCut := [⟨41,303022205,303022411⟩,
⟨98,723562383,723562884⟩,
⟨128,939300697,939301348⟩]
theorem checked14094 : checkPrefixCuts (2^48) 1851260929 9 Manual.Count131072.C014094.packed 128 cuts14094 = true := by
 decide +kernel
def pointBounds14094 : List (Nat × Nat × Nat) := [(1851302912,95450237721094,95450615200301),(1851361280,95450658261272,95451035740774)]
theorem point_links_checked14094 : (cuts14094.take 2).map (fun c => (1851260929-1+2*2^9*c.k,95449934698889+c.lower,95450312177890+c.upper)) = pointBounds14094 := by
 decide +kernel
def cuts14095 : List PrefixCut := [⟨27,193842160,193842296⟩,
⟨84,615876149,615876577⟩,
⟨128,934369088,934369734⟩]
theorem checked14095 : checkPrefixCuts (2^48) 1851392001 9 Manual.Count131072.C014095.packed 128 cuts14095 = true := by
 decide +kernel
def pointBounds14095 : List (Nat × Nat × Nat) := [(1851419648,95451067841746,95451445321534),(1851478016,95451489875735,95451867355815)]
theorem point_links_checked14095 : (cuts14095.take 2).map (fun c => (1851392001-1+2*2^9*c.k,95450873999586+c.lower,95451251479238+c.upper)) = pointBounds14095 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000127
