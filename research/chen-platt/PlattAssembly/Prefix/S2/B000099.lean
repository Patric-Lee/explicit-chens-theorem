import PlattAssemblyKernel
import PlattCertificates.Count131072.C013168
import PlattCertificates.Count131072.C013169
import PlattCertificates.Count131072.C013170
import PlattCertificates.Count131072.C013171
import PlattCertificates.Count131072.C013172
import PlattCertificates.Count131072.C013173
import PlattCertificates.Count131072.C013174
import PlattCertificates.Count131072.C013175
import PlattCertificates.Count131072.C013176
import PlattCertificates.Count131072.C013177
import PlattCertificates.Count131072.C013178
import PlattCertificates.Count131072.C013179
import PlattCertificates.Count131072.C013180
import PlattCertificates.Count131072.C013181
import PlattCertificates.Count131072.C013182
import PlattCertificates.Count131072.C013183
import PlattCertificates.Count131072.C013184
import PlattCertificates.Count131072.C013185
import PlattCertificates.Count131072.C013186
import PlattCertificates.Count131072.C013187
import PlattCertificates.Count131072.C013188
import PlattCertificates.Count131072.C013189
import PlattCertificates.Count131072.C013190
import PlattCertificates.Count131072.C013191
import PlattCertificates.Count131072.C013192
import PlattCertificates.Count131072.C013193
import PlattCertificates.Count131072.C013194
import PlattCertificates.Count131072.C013195
import PlattCertificates.Count131072.C013196
import PlattCertificates.Count131072.C013197
import PlattCertificates.Count131072.C013198
import PlattCertificates.Count131072.C013199
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000099
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts13168 : List PrefixCut := [⟨36,285232379,285232580⟩,
⟨89,697205745,697206239⟩,
⟨128,1001947127,1001947840⟩]
theorem checked13168 : checkPrefixCuts (2^48) 1729888257 9 Manual.Count131072.C013168.packed 128 cuts13168 = true := by
 decide +kernel
def pointBounds13168 : List (Nat × Nat × Nat) := [(1729925120,94554434416105,94554811263934),(1729979392,94554846389471,94555223237593)]
theorem point_links_checked13168 : (cuts13168.take 2).map (fun c => (1729888257-1+2*2^9*c.k,94554149183726+c.lower,94554526031354+c.upper)) = pointBounds13168 := by
 decide +kernel
def cuts13169 : List PrefixCut := [⟨14,109659640,109659720⟩,
⟨67,514611317,514611690⟩,
⟨120,923780230,923780897⟩,
⟨128,984625722,984626433⟩]
theorem checked13169 : checkPrefixCuts (2^48) 1730019329 9 Manual.Count131072.C013169.packed 128 cuts13169 = true := by
 decide +kernel
def pointBounds13169 : List (Nat × Nat × Nat) := [(1730033664,94555260790493,94555637638914),(1730087936,94555665742170,94556042590884),(1730142208,94556074911083,94556451760091)]
theorem point_links_checked13169 : (cuts13169.take 3).map (fun c => (1730019329-1+2*2^9*c.k,94555151130853+c.lower,94555527979194+c.upper)) = pointBounds13169 := by
 decide +kernel
def cuts13170 : List PrefixCut := [⟨45,345544925,345545176⟩,
⟨98,761358141,761358694⟩,
⟨128,994149187,994149908⟩]
theorem checked13170 : checkPrefixCuts (2^48) 1730150401 9 Manual.Count131072.C013170.packed 128 cuts13170 = true := by
 decide +kernel
def pointBounds13170 : List (Nat × Nat × Nat) := [(1730196480,94556481301500,94556858150803),(1730250752,94556897114716,94557273964321)]
theorem point_links_checked13170 : (cuts13170.take 2).map (fun c => (1730150401-1+2*2^9*c.k,94556135756575+c.lower,94556512605627+c.upper)) = pointBounds13170 := by
 decide +kernel
def cuts13171 : List PrefixCut := [⟨23,177315410,177315535⟩,
⟨76,589686483,589686907⟩,
⟨128,998953979,998954702⟩]
theorem checked13171 : checkPrefixCuts (2^48) 1730281473 9 Manual.Count131072.C013171.packed 128 cuts13171 = true := by
 decide +kernel
def pointBounds13171 : List (Nat × Nat × Nat) := [(1730305024,94557307221172,94557684071070),(1730359296,94557719592245,94558096442442)]
theorem point_links_checked13171 : (cuts13171.take 2).map (fun c => (1730281473-1+2*2^9*c.k,94557129905762+c.lower,94557506755535+c.upper)) = pointBounds13171 := by
 decide +kernel
def cuts13172 : List PrefixCut := [⟨1,8621160,8621166⟩,
⟨54,421779618,421779917⟩,
⟨107,826629672,826630263⟩,
⟨128,994974619,994975331⟩]
theorem checked13172 : checkPrefixCuts (2^48) 1730412545 9 Manual.Count131072.C013172.packed 128 cuts13172 = true := by
 decide +kernel
def pointBounds13172 : List (Nat × Nat × Nat) := [(1730413568,94558137480901,94558514331403),(1730467840,94558550639359,94558927490154),(1730522112,94558955489413,94559332340500)]
theorem point_links_checked13172 : (cuts13172.take 3).map (fun c => (1730412545-1+2*2^9*c.k,94558128859741+c.lower,94558505710237+c.upper)) = pointBounds13172 := by
 decide +kernel
def cuts13173 : List PrefixCut := [⟨32,253408014,253408197⟩,
⟨85,674171893,674172377⟩,
⟨128,1014091362,1014092091⟩]
theorem checked13173 : checkPrefixCuts (2^48) 1730543617 9 Manual.Count131072.C013173.packed 128 cuts13173 = true := by
 decide +kernel
def pointBounds13173 : List (Nat × Nat × Nat) := [(1730576384,94559377242374,94559754093765),(1730630656,94559798006253,94560174857945)]
theorem point_links_checked13173 : (cuts13173.take 2).map (fun c => (1730543617-1+2*2^9*c.k,94559123834360+c.lower,94559500685568+c.upper)) = pointBounds13173 := by
 decide +kernel
def cuts13174 : List PrefixCut := [⟨10,78391675,78391732⟩,
⟨63,496527092,496527450⟩,
⟨116,910583607,910584262⟩,
⟨128,1009948743,1009949469⟩]
theorem checked13174 : checkPrefixCuts (2^48) 1730674689 9 Manual.Count131072.C013174.packed 128 cuts13174 = true := by
 decide +kernel
def pointBounds13174 : List (Nat × Nat × Nat) := [(1730684928,94560216317397,94560593169391),(1730739200,94560634452814,94561011305109),(1730793472,94561048509329,94561425361921)]
theorem point_links_checked13174 : (cuts13174.take 3).map (fun c => (1730674689-1+2*2^9*c.k,94560137925722+c.lower,94560514777659+c.upper)) = pointBounds13174 := by
 decide +kernel
def cuts13175 : List PrefixCut := [⟨41,315979481,315979711⟩,
⟨94,727408088,727408621⟩,
⟨128,989544795,989545521⟩]
theorem checked13175 : checkPrefixCuts (2^48) 1730805761 9 Manual.Count131072.C013175.packed 128 cuts13175 = true := by
 decide +kernel
def pointBounds13175 : List (Nat × Nat × Nat) := [(1730847744,94561463853946,94561840706839),(1730902016,94561875282553,94562252135749)]
theorem point_links_checked13175 : (cuts13175.take 2).map (fun c => (1730805761-1+2*2^9*c.k,94561147874465+c.lower,94561524727128+c.upper)) = pointBounds13175 := by
 decide +kernel
def cuts13176 : List PrefixCut := [⟨19,157084412,157084520⟩,
⟨72,580682979,580683389⟩,
⟨125,991585091,991585798⟩,
⟨128,1015812789,1015813513⟩]
theorem checked13176 : checkPrefixCuts (2^48) 1730936833 9 Manual.Count131072.C013176.packed 128 cuts13176 = true := by
 decide +kernel
def pointBounds13176 : List (Nat × Nat × Nat) := [(1730956288,94562294503672,94562671357169),(1731010560,94562718102239,94563094956038),(1731064832,94563129004351,94563505858447)]
theorem point_links_checked13176 : (cuts13176.take 3).map (fun c => (1730936833-1+2*2^9*c.k,94562137419260+c.lower,94562514272649+c.upper)) = pointBounds13176 := by
 decide +kernel
def cuts13177 : List PrefixCut := [⟨50,390563852,390564130⟩,
⟨103,810870654,810871233⟩,
⟨128,1006467302,1006468022⟩]
theorem checked13177 : checkPrefixCuts (2^48) 1731067905 9 Manual.Count131072.C013177.packed 128 cuts13177 = true := by
 decide +kernel
def pointBounds13177 : List (Nat × Nat × Nat) := [(1731119104,94563543795901,94563920650292),(1731173376,94563964102703,94564340957395)]
theorem point_links_checked13177 : (cuts13177.take 2).map (fun c => (1731067905-1+2*2^9*c.k,94563153232049+c.lower,94563530086162+c.upper)) = pointBounds13177 := by
 decide +kernel
def cuts13178 : List PrefixCut := [⟨28,212015077,212015232⟩,
⟨81,632945956,632946414⟩,
⟨128,991108610,991109326⟩]
theorem checked13178 : checkPrefixCuts (2^48) 1731198977 9 Manual.Count131072.C013178.packed 128 cuts13178 = true := by
 decide +kernel
def pointBounds13178 : List (Nat × Nat × Nat) := [(1731227648,94564371714428,94564748569416),(1731281920,94564792645307,94565169500598)]
theorem point_links_checked13178 : (cuts13178.take 2).map (fun c => (1731198977-1+2*2^9*c.k,94564159699351+c.lower,94564536554184+c.upper)) = pointBounds13178 := by
 decide +kernel
def cuts13179 : List PrefixCut := [⟨6,46171858,46171890⟩,
⟨59,454883117,454883442⟩,
⟨112,863256446,863257065⟩,
⟨128,991033094,991033806⟩]
theorem checked13179 : checkPrefixCuts (2^48) 1731330049 9 Manual.Count131072.C013179.packed 128 cuts13179 = true := by
 decide +kernel
def pointBounds13179 : List (Nat × Nat × Nat) := [(1731336192,94565196979819,94565573835400),(1731390464,94565605691078,94565982546952),(1731444736,94566014064407,94566390920575)]
theorem point_links_checked13179 : (cuts13179.take 3).map (fun c => (1731330049-1+2*2^9*c.k,94565150807961+c.lower,94565527663510+c.upper)) = pointBounds13179 := by
 decide +kernel
def cuts13180 : List PrefixCut := [⟨37,284160370,284160574⟩,
⟨90,692995866,692996362⟩,
⟨128,990145433,990146145⟩]
theorem checked13180 : checkPrefixCuts (2^48) 1731461121 9 Manual.Count131072.C013180.packed 128 cuts13180 = true := by
 decide +kernel
def pointBounds13180 : List (Nat × Nat × Nat) := [(1731499008,94566426001425,94566802857890),(1731553280,94566834836921,94567211693678)]
theorem point_links_checked13180 : (cuts13180.take 2).map (fun c => (1731461121-1+2*2^9*c.k,94566141841055+c.lower,94566518697316+c.upper)) = pointBounds13180 := by
 decide +kernel
def cuts13181 : List PrefixCut := [⟨15,117037393,117037475⟩,
⟨68,534949926,534950306⟩,
⟨121,952036747,952037433⟩,
⟨128,1007300575,1007301302⟩]
theorem checked13181 : checkPrefixCuts (2^48) 1731592193 9 Manual.Count131072.C013181.packed 128 cuts13181 = true := by
 decide +kernel
def pointBounds13181 : List (Nat × Nat × Nat) := [(1731607552,94567249023881,94567625880936),(1731661824,94567666936414,94568043793767),(1731716096,94568084023235,94568460880894)]
theorem point_links_checked13181 : (cuts13181.take 3).map (fun c => (1731592193-1+2*2^9*c.k,94567131986488+c.lower,94567508843461+c.upper)) = pointBounds13181 := by
 decide +kernel
def cuts13182 : List PrefixCut := [⟨46,362460068,362460336⟩,
⟨99,769931198,769931759⟩,
⟨128,999747812,999748538⟩]
theorem checked13182 : checkPrefixCuts (2^48) 1731723265 9 Manual.Count131072.C013182.packed 128 cuts13182 = true := by
 decide +kernel
def pointBounds13182 : List (Nat × Nat × Nat) := [(1731770368,94568501747131,94568878605099),(1731824640,94568909218261,94569286076522)]
theorem point_links_checked13182 : (cuts13182.take 2).map (fun c => (1731723265-1+2*2^9*c.k,94568139287063+c.lower,94568516144763+c.upper)) = pointBounds13182 := by
 decide +kernel
def cuts13183 : List PrefixCut := [⟨24,188206106,188206242⟩,
⟨77,599389767,599390199⟩,
⟨128,1003734965,1003735687⟩]
theorem checked13183 : checkPrefixCuts (2^48) 1731854337 9 Manual.Count131072.C013183.packed 128 cuts13183 = true := by
 decide +kernel
def pointBounds13183 : List (Nat × Nat × Nat) := [(1731878912,94569327240981,94569704099543),(1731933184,94569738424642,94570115283500)]
theorem point_links_checked13183 : (cuts13183.take 2).map (fun c => (1731854337-1+2*2^9*c.k,94569139034875+c.lower,94569515893301+c.upper)) = pointBounds13183 := by
 decide +kernel
def cuts13184 : List PrefixCut := [⟨2,16089048,16089059⟩,
⟨55,434885039,434885352⟩,
⟨108,843104850,843105454⟩,
⟨128,1000896636,1000897350⟩]
theorem checked13184 : checkPrefixCuts (2^48) 1731985409 9 Manual.Count131072.C013184.packed 128 cuts13184 = true := by
 decide +kernel
def pointBounds13184 : List (Nat × Nat × Nat) := [(1731987456,94570158858888,94570535718047),(1732041728,94570577654879,94570954514340),(1732096000,94570985874690,94571362734442)]
theorem point_links_checked13184 : (cuts13184.take 3).map (fun c => (1731985409-1+2*2^9*c.k,94570142769840+c.lower,94570519628988+c.upper)) = pointBounds13184 := by
 decide +kernel
def cuts13185 : List PrefixCut := [⟨33,252527838,252528020⟩,
⟨86,671121891,671122373⟩,
⟨128,994158251,994158968⟩]
theorem checked13185 : checkPrefixCuts (2^48) 1732116481 9 Manual.Count131072.C013185.packed 128 cuts13185 = true := by
 decide +kernel
def pointBounds13185 : List (Nat × Nat × Nat) := [(1732150272,94571396194314,94571773054358),(1732204544,94571814788367,94572191648711)]
theorem point_links_checked13185 : (cuts13185.take 2).map (fun c => (1732116481-1+2*2^9*c.k,94571143666476+c.lower,94571520526338+c.upper)) = pointBounds13185 := by
 decide +kernel
def cuts13186 : List PrefixCut := [⟨11,85632548,85632611⟩,
⟨64,508100146,508100517⟩,
⟨117,929417139,929417810⟩,
⟨128,1011794183,1011794910⟩]
theorem checked13186 : checkPrefixCuts (2^48) 1732247553 9 Manual.Count131072.C013186.packed 128 cuts13186 = true := by
 decide +kernel
def pointBounds13186 : List (Nat × Nat × Nat) := [(1732258816,94572223457275,94572600317917),(1732313088,94572645924873,94573022785823),(1732367360,94573067241866,94573444103116)]
theorem point_links_checked13186 : (cuts13186.take 3).map (fun c => (1732247553-1+2*2^9*c.k,94572137824727+c.lower,94572514685306+c.upper)) = pointBounds13186 := by
 decide +kernel
def cuts13187 : List PrefixCut := [⟨42,332427588,332427823⟩,
⟨95,736658652,736659179⟩,
⟨128,988159374,988160083⟩]
theorem checked13187 : checkPrefixCuts (2^48) 1732378625 9 Manual.Count131072.C013187.packed 128 cuts13187 = true := by
 decide +kernel
def pointBounds13187 : List (Nat × Nat × Nat) := [(1732421632,94573482046498,94573858908039),(1732475904,94573886277562,94574263139395)]
theorem point_links_checked13187 : (cuts13187.take 2).map (fun c => (1732378625-1+2*2^9*c.k,94573149618910+c.lower,94573526480216+c.upper)) = pointBounds13187 := by
 decide +kernel
def cuts13188 : List PrefixCut := [⟨20,150280676,150280786⟩,
⟨73,563746733,563747142⟩,
⟨126,986459913,986460620⟩,
⟨128,1003680075,1003680793⟩]
theorem checked13188 : checkPrefixCuts (2^48) 1732509697 9 Manual.Count131072.C013188.packed 128 cuts13188 = true := by
 decide +kernel
def pointBounds13188 : List (Nat × Nat × Nat) := [(1732530176,94574288058960,94574664921085),(1732584448,94574701525017,94575078387441),(1732638720,94575124238197,94575501100919)]
theorem point_links_checked13188 : (cuts13188.take 3).map (fun c => (1732509697-1+2*2^9*c.k,94574137778284+c.lower,94574514640299+c.upper)) = pointBounds13188 := by
 decide +kernel
def cuts13189 : List PrefixCut := [⟨51,394595407,394595687⟩,
⟨104,816632248,816632829⟩,
⟨128,1000355384,1000356098⟩]
theorem checked13189 : checkPrefixCuts (2^48) 1732640769 9 Manual.Count131072.C013189.packed 128 cuts13189 = true := by
 decide +kernel
def pointBounds13189 : List (Nat × Nat × Nat) := [(1732692992,94575536053766,94575912916779),(1732747264,94575958090607,94576334953921)]
theorem point_links_checked13189 : (cuts13189.take 2).map (fun c => (1732640769-1+2*2^9*c.k,94575141458359+c.lower,94575518321092+c.upper)) = pointBounds13189 := by
 decide +kernel
def cuts13190 : List PrefixCut := [⟨29,223680698,223680858⟩,
⟨82,636594640,636595099⟩,
⟨128,993782418,993783131⟩]
theorem checked13190 : checkPrefixCuts (2^48) 1732771841 9 Manual.Count131072.C013190.packed 128 cuts13190 = true := by
 decide +kernel
def pointBounds13190 : List (Nat × Nat × Nat) := [(1732801536,94576365494441,94576742358048),(1732855808,94576778408383,94577155272289)]
theorem point_links_checked13190 : (cuts13190.take 2).map (fun c => (1732771841-1+2*2^9*c.k,94576141813743+c.lower,94576518677190+c.upper)) = pointBounds13190 := by
 decide +kernel
def cuts13191 : List PrefixCut := [⟨7,53114399,53114436⟩,
⟨60,464865531,464865864⟩,
⟨113,879527381,879528009⟩,
⟨128,994681844,994682553⟩]
theorem checked13191 : checkPrefixCuts (2^48) 1732902913 9 Manual.Count131072.C013191.packed 128 cuts13191 = true := by
 decide +kernel
def pointBounds13191 : List (Nat × Nat × Nat) := [(1732910080,94577188710560,94577565574757),(1732964352,94577600461692,94577977326185),(1733018624,94578015123542,94578391988330)]
theorem point_links_checked13191 : (cuts13191.take 3).map (fun c => (1732902913-1+2*2^9*c.k,94577135596161+c.lower,94577512460321+c.upper)) = pointBounds13191 := by
 decide +kernel
def cuts13192 : List PrefixCut := [⟨38,303392320,303392536⟩,
⟨91,729234526,729235044⟩,
⟨128,1021242117,1021242843⟩]
theorem checked13192 : checkPrefixCuts (2^48) 1733033985 9 Manual.Count131072.C013192.packed 128 cuts13192 = true := by
 decide +kernel
def pointBounds13192 : List (Nat × Nat × Nat) := [(1733072896,94578433670325,94578810535410),(1733127168,94578859512531,94579236377918)]
theorem point_links_checked13192 : (cuts13192.take 2).map (fun c => (1733033985-1+2*2^9*c.k,94578130278005+c.lower,94578507142874+c.upper)) = pointBounds13192 := by
 decide +kernel
def cuts13193 : List PrefixCut := [⟨16,126025786,126025875⟩,
⟨69,548593336,548593729⟩,
⟨122,957181607,957182289⟩,
⟨128,1005412362,1005413079⟩]
theorem checked13193 : checkPrefixCuts (2^48) 1733165057 9 Manual.Count131072.C013193.packed 128 cuts13193 = true := by
 decide +kernel
def pointBounds13193 : List (Nat × Nat × Nat) := [(1733181440,94579277545908,94579654411592),(1733235712,94579700113458,94580076979446),(1733289984,94580108701729,94580485568006)]
theorem point_links_checked13193 : (cuts13193.take 3).map (fun c => (1733165057-1+2*2^9*c.k,94579151520122+c.lower,94579528385717+c.upper)) = pointBounds13193 := by
 decide +kernel
def cuts13194 : List PrefixCut := [⟨47,364891609,364891873⟩,
⟨100,775890073,775890633⟩,
⟨128,996079935,996080651⟩]
theorem checked13194 : checkPrefixCuts (2^48) 1733296129 9 Manual.Count131072.C013194.packed 128 cuts13194 = true := by
 decide +kernel
def pointBounds13194 : List (Nat × Nat × Nat) := [(1733344256,94580521824093,94580898690669),(1733398528,94580932822557,94581309689429)]
theorem point_links_checked13194 : (cuts13194.take 2).map (fun c => (1733296129-1+2*2^9*c.k,94580156932484+c.lower,94580533798796+c.upper)) = pointBounds13194 := by
 decide +kernel
def cuts13195 : List PrefixCut := [⟨25,190795755,190795890⟩,
⟨78,606152585,606153018⟩,
⟨128,998440185,998440899⟩]
theorem checked13195 : checkPrefixCuts (2^48) 1733427201 9 Manual.Count131072.C013195.packed 128 cuts13195 = true := by
 decide +kernel
def pointBounds13195 : List (Nat × Nat × Nat) := [(1733452800,94581343808174,94581720675337),(1733507072,94581759165004,94582136032465)]
theorem point_links_checked13195 : (cuts13195.take 2).map (fun c => (1733427201-1+2*2^9*c.k,94581153012419+c.lower,94581529879447+c.upper)) = pointBounds13195 := by
 decide +kernel
def cuts13196 : List PrefixCut := [⟨3,24517588,24517606⟩,
⟨56,433516224,433516534⟩,
⟨109,845099723,845100329⟩,
⟨128,996253991,996254703⟩]
theorem checked13196 : checkPrefixCuts (2^48) 1733558273 9 Manual.Count131072.C013196.packed 128 cuts13196 = true := by
 decide +kernel
def pointBounds13196 : List (Nat × Nat × Nat) := [(1733561344,94582175970192,94582552837952),(1733615616,94582584968828,94582961836880),(1733669888,94582996552327,94583373420675)]
theorem point_links_checked13196 : (cuts13196.take 3).map (fun c => (1733558273-1+2*2^9*c.k,94582151452604+c.lower,94582528320346+c.upper)) = pointBounds13196 := by
 decide +kernel
def cuts13197 : List PrefixCut := [⟨34,267722347,267722540⟩,
⟨87,674409626,674410108⟩,
⟨128,998126945,998127660⟩]
theorem checked13197 : checkPrefixCuts (2^48) 1733689345 9 Manual.Count131072.C013197.packed 128 cuts13197 = true := by
 decide +kernel
def pointBounds13197 : List (Nat × Nat × Nat) := [(1733724160,94583415428942,94583792297589),(1733778432,94583822116221,94584198985157)]
theorem point_links_checked13197 : (cuts13197.take 2).map (fun c => (1733689345-1+2*2^9*c.k,94583147706595+c.lower,94583524575049+c.upper)) = pointBounds13197 := by
 decide +kernel
def cuts13198 : List PrefixCut := [⟨12,91723879,91723945⟩,
⟨65,502931209,502931572⟩,
⟨118,916398250,916398908⟩,
⟨128,992207260,992207973⟩]
theorem checked13198 : checkPrefixCuts (2^48) 1733820417 9 Manual.Count131072.C013198.packed 128 cuts13198 = true := by
 decide +kernel
def pointBounds13198 : List (Nat × Nat × Nat) := [(1733832704,94584237557419,94584614426654),(1733886976,94584648764749,94585025634281),(1733941248,94585062231790,94585439101617)]
theorem point_links_checked13198 : (cuts13198.take 3).map (fun c => (1733820417-1+2*2^9*c.k,94584145833540+c.lower,94584522702709+c.upper)) = pointBounds13198 := by
 decide +kernel
def cuts13199 : List PrefixCut := [⟨43,339917831,339918074⟩,
⟨96,746216786,746217325⟩,
⟨128,993268961,993269682⟩]
theorem checked13199 : checkPrefixCuts (2^48) 1733951489 9 Manual.Count131072.C013199.packed 128 cuts13199 = true := by
 decide +kernel
def pointBounds13199 : List (Nat × Nat × Nat) := [(1733995520,94585477958631,94585854828756),(1734049792,94585884257586,94586261128007)]
theorem point_links_checked13199 : (cuts13199.take 2).map (fun c => (1733951489-1+2*2^9*c.k,94585138040800+c.lower,94585514910682+c.upper)) = pointBounds13199 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000099
