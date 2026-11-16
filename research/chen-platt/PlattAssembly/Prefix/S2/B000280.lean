import PlattAssemblyKernel
import PlattCertificates.Count131072.C018960
import PlattCertificates.Count131072.C018961
import PlattCertificates.Count131072.C018962
import PlattCertificates.Count131072.C018963
import PlattCertificates.Count131072.C018964
import PlattCertificates.Count131072.C018965
import PlattCertificates.Count131072.C018966
import PlattCertificates.Count131072.C018967
import PlattCertificates.Count131072.C018968
import PlattCertificates.Count131072.C018969
import PlattCertificates.Count131072.C018970
import PlattCertificates.Count131072.C018971
import PlattCertificates.Count131072.C018972
import PlattCertificates.Count131072.C018973
import PlattCertificates.Count131072.C018974
import PlattCertificates.Count131072.C018975
import PlattCertificates.Count131072.C018976
import PlattCertificates.Count131072.C018977
import PlattCertificates.Count131072.C018978
import PlattCertificates.Count131072.C018979
import PlattCertificates.Count131072.C018980
import PlattCertificates.Count131072.C018981
import PlattCertificates.Count131072.C018982
import PlattCertificates.Count131072.C018983
import PlattCertificates.Count131072.C018984
import PlattCertificates.Count131072.C018985
import PlattCertificates.Count131072.C018986
import PlattCertificates.Count131072.C018987
import PlattCertificates.Count131072.C018988
import PlattCertificates.Count131072.C018989
import PlattCertificates.Count131072.C018990
import PlattCertificates.Count131072.C018991
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000280
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts18960 : List PrefixCut := [⟨26,138980646,138980727⟩,
⟨102,544153333,544153653⟩,
⟨128,681997365,681997768⟩]
theorem checked18960 : checkPrefixCuts (2^48) 2489057281 9 Manual.Count131072.C018960.packed 128 cuts18960 = true := by
 decide +kernel
def pointBounds18960 : List (Nat × Nat × Nat) := [(2489083904,99328084268671,99328464227587),(2489161728,99328489441358,99328869400513)]
theorem point_links_checked18960 : (cuts18960.take 2).map (fun c => (2489057281-1+2*2^9*c.k,99327945288025+c.lower,99328325246860+c.upper)) = pointBounds18960 := by
 decide +kernel
def cuts18961 : List PrefixCut := [⟨50,268785964,268786119⟩,
⟨126,675742437,675742835⟩,
⟨128,685692868,685693272⟩]
theorem checked18961 : checkPrefixCuts (2^48) 2489188353 9 Manual.Count131072.C018961.packed 128 cuts18961 = true := by
 decide +kernel
def pointBounds18961 : List (Nat × Nat × Nat) := [(2489239552,99328896071354,99329276030747),(2489317376,99329303027827,99329682987463)]
theorem point_links_checked18961 : (cuts18961.take 2).map (fun c => (2489188353-1+2*2^9*c.k,99328627285390+c.lower,99329007244628+c.upper)) = pointBounds18961 := by
 decide +kernel
def cuts18962 : List PrefixCut := [⟨74,392470481,392470717⟩,
⟨128,676272007,676272417⟩]
theorem checked18962 : checkPrefixCuts (2^48) 2489319425 9 Manual.Count131072.C018962.packed 128 cuts18962 = true := by
 decide +kernel
def pointBounds18962 : List (Nat × Nat × Nat) := [(2489395200,99329705448739,99330085408617)]
theorem point_links_checked18962 : (cuts18962.take 1).map (fun c => (2489319425-1+2*2^9*c.k,99329312978258+c.lower,99329692937900+c.upper)) = pointBounds18962 := by
 decide +kernel
def cuts18963 : List PrefixCut := [⟨22,113405766,113405834⟩,
⟨98,521680879,521681189⟩,
⟨128,679289062,679289466⟩]
theorem checked18963 : checkPrefixCuts (2^48) 2489450497 9 Manual.Count131072.C018963.packed 128 cuts18963 = true := by
 decide +kernel
def pointBounds18963 : List (Nat × Nat × Nat) := [(2489473024,99330102656031,99330482616151),(2489550848,99330510931144,99330890891506)]
theorem point_links_checked18963 : (cuts18963.take 2).map (fun c => (2489450497-1+2*2^9*c.k,99329989250265+c.lower,99330369210317+c.upper)) = pointBounds18963 := by
 decide +kernel
def cuts18964 : List PrefixCut := [⟨46,242626841,242626991⟩,
⟨122,644771339,644771731⟩,
⟨128,678348766,678349178⟩]
theorem checked18964 : checkPrefixCuts (2^48) 2489581569 9 Manual.Count131072.C018964.packed 128 cuts18964 = true := by
 decide +kernel
def pointBounds18964 : List (Nat × Nat × Nat) := [(2489628672,99330911166168,99331291126774),(2489706496,99331313310666,99331693271514)]
theorem point_links_checked18964 : (cuts18964.take 2).map (fun c => (2489581569-1+2*2^9*c.k,99330668539327+c.lower,99331048499783+c.upper)) = pointBounds18964 := by
 decide +kernel
def cuts18965 : List PrefixCut := [⟨70,370476463,370476678⟩,
⟨128,681704636,681705039⟩]
theorem checked18965 : checkPrefixCuts (2^48) 2489712641 9 Manual.Count131072.C018965.packed 128 cuts18965 = true := by
 decide +kernel
def pointBounds18965 : List (Nat × Nat × Nat) := [(2489784320,99331717364556,99332097325639)]
theorem point_links_checked18965 : (cuts18965.take 1).map (fun c => (2489712641-1+2*2^9*c.k,99331346888093+c.lower,99331726848961+c.upper)) = pointBounds18965 := by
 decide +kernel
def cuts18966 : List PrefixCut := [⟨18,98126362,98126419⟩,
⟨94,506111570,506111867⟩,
⟨128,691616865,691617267⟩]
theorem checked18966 : checkPrefixCuts (2^48) 2489843713 9 Manual.Count131072.C018966.packed 128 cuts18966 = true := by
 decide +kernel
def pointBounds18966 : List (Nat × Nat × Nat) := [(2489862144,99332126719091,99332506680419),(2489939968,99332534704299,99332914665867)]
theorem point_links_checked18966 : (cuts18966.take 2).map (fun c => (2489843713-1+2*2^9*c.k,99332028592729+c.lower,99332408554000+c.upper)) = pointBounds18966 := by
 decide +kernel
def cuts18967 : List PrefixCut := [⟨42,219980259,219980391⟩,
⟨118,633478968,633479345⟩,
⟨128,687850032,687850441⟩]
theorem checked18967 : checkPrefixCuts (2^48) 2489974785 9 Manual.Count131072.C018967.packed 128 cuts18967 = true := by
 decide +kernel
def pointBounds18967 : List (Nat × Nat × Nat) := [(2490017792,99332940189853,99333320151658),(2490095616,99333353688562,99333733650612)]
theorem point_links_checked18967 : (cuts18967.take 2).map (fun c => (2489974785-1+2*2^9*c.k,99332720209594+c.lower,99333100171267+c.upper)) = pointBounds18967 := by
 decide +kernel
def cuts18968 : List PrefixCut := [⟨66,344420089,344420299⟩,
⟨128,676623551,676623958⟩]
theorem checked18968 : checkPrefixCuts (2^48) 2490105857 9 Manual.Count131072.C018968.packed 128 cuts18968 = true := by
 decide +kernel
def pointBounds18968 : List (Nat × Nat × Nat) := [(2490173440,99333752479715,99334132442007)]
theorem point_links_checked18968 : (cuts18968.take 1).map (fun c => (2490105857-1+2*2^9*c.k,99333408059626+c.lower,99333788021708+c.upper)) = pointBounds18968 := by
 decide +kernel
def cuts18969 : List PrefixCut := [⟨14,74713519,74713565⟩,
⟨90,480600522,480600815⟩,
⟨128,682578518,682578929⟩]
theorem checked18969 : checkPrefixCuts (2^48) 2490236929 9 Manual.Count131072.C018969.packed 128 cuts18969 = true := by
 decide +kernel
def pointBounds18969 : List (Nat × Nat × Nat) := [(2490251264,99334159396696,99334539359231),(2490329088,99334565283699,99334945246481)]
theorem point_links_checked18969 : (cuts18969.take 2).map (fun c => (2490236929-1+2*2^9*c.k,99334084683177+c.lower,99334464645666+c.upper)) = pointBounds18969 := by
 decide +kernel
def cuts18970 : List PrefixCut := [⟨38,202200891,202201013⟩,
⟨115,616765107,616765481⟩,
⟨128,686950396,686950810⟩]
theorem checked18970 : checkPrefixCuts (2^48) 2490368001 9 Manual.Count131072.C018970.packed 128 cuts18970 = true := by
 decide +kernel
def pointBounds18970 : List (Nat × Nat × Nat) := [(2490406912,99334969462586,99335349425608),(2490485760,99335384026802,99335763990076)]
theorem point_links_checked18970 : (cuts18970.take 2).map (fun c => (2490368001-1+2*2^9*c.k,99334767261695+c.lower,99335147224595+c.upper)) = pointBounds18970 := by
 decide +kernel
def cuts18971 : List PrefixCut := [⟨64,335211340,335211544⟩,
⟨128,676742705,676743116⟩]
theorem checked18971 : checkPrefixCuts (2^48) 2490499073 9 Manual.Count131072.C018971.packed 128 cuts18971 = true := by
 decide +kernel
def pointBounds18971 : List (Nat × Nat × Nat) := [(2490564608,99335789423431,99336169386949)]
theorem point_links_checked18971 : (cuts18971.take 1).map (fun c => (2490499073-1+2*2^9*c.k,99335454212091+c.lower,99335834175405+c.upper)) = pointBounds18971 := by
 decide +kernel
def cuts18972 : List PrefixCut := [⟨13,69390114,69390157⟩,
⟨90,485610102,485610395⟩,
⟨128,688573284,688573697⟩]
theorem checked18972 : checkPrefixCuts (2^48) 2490630145 9 Manual.Count131072.C018972.packed 128 cuts18972 = true := by
 decide +kernel
def pointBounds18972 : List (Nat × Nat × Nat) := [(2490643456,99336200344910,99336580308678),(2490722304,99336616564898,99336996528916)]
theorem point_links_checked18972 : (cuts18972.take 2).map (fun c => (2490630145-1+2*2^9*c.k,99336130954796+c.lower,99336510918521+c.upper)) = pointBounds18972 := by
 decide +kernel
def cuts18973 : List PrefixCut := [⟨39,206011171,206011294⟩,
⟨116,614746602,614746969⟩,
⟨128,680400710,680401117⟩]
theorem checked18973 : checkPrefixCuts (2^48) 2490761217 9 Manual.Count131072.C018973.packed 128 cuts18973 = true := by
 decide +kernel
def pointBounds18973 : List (Nat × Nat × Nat) := [(2490801152,99337025539251,99337405503512),(2490880000,99337434274682,99337814239187)]
theorem point_links_checked18973 : (cuts18973.take 2).map (fun c => (2490761217-1+2*2^9*c.k,99336819528080+c.lower,99337199492218+c.upper)) = pointBounds18973 := by
 decide +kernel
def cuts18974 : List PrefixCut := [⟨65,345328357,345328561⟩,
⟨128,685223754,685224156⟩]
theorem checked18974 : checkPrefixCuts (2^48) 2490892289 9 Manual.Count131072.C018974.packed 128 cuts18974 = true := by
 decide +kernel
def pointBounds18974 : List (Nat × Nat × Nat) := [(2490958848,99337845257147,99338225221896)]
theorem point_links_checked18974 : (cuts18974.take 1).map (fun c => (2490892289-1+2*2^9*c.k,99337499928790+c.lower,99337879893335+c.upper)) = pointBounds18974 := by
 decide +kernel
def cuts18975 : List PrefixCut := [⟨14,76723852,76723896⟩,
⟨91,484516493,484516783⟩,
⟨128,682137029,682137438⟩]
theorem checked18975 : checkPrefixCuts (2^48) 2491023361 9 Manual.Count131072.C018975.packed 128 cuts18975 = true := by
 decide +kernel
def pointBounds18975 : List (Nat × Nat × Nat) := [(2491037696,99338261876396,99338641841387),(2491116544,99338669669037,99339049634274)]
theorem point_links_checked18975 : (cuts18975.take 2).map (fun c => (2491023361-1+2*2^9*c.k,99338185152544+c.lower,99338565117491+c.upper)) = pointBounds18975 := by
 decide +kernel
def cuts18976 : List PrefixCut := [⟨40,210837094,210837219⟩,
⟨117,618603939,618604313⟩,
⟨128,678598468,678598877⟩]
theorem checked18976 : checkPrefixCuts (2^48) 2491154433 9 Manual.Count131072.C018976.packed 128 cuts18976 = true := by
 decide +kernel
def pointBounds18976 : List (Nat × Nat × Nat) := [(2491195392,99339078126667,99339458092148),(2491274240,99339485893512,99339865859242)]
theorem point_links_checked18976 : (cuts18976.take 2).map (fun c => (2491154433-1+2*2^9*c.k,99338867289573+c.lower,99339247254929+c.upper)) = pointBounds18976 := by
 decide +kernel
def cuts18977 : List PrefixCut := [⟨66,357023950,357024164⟩,
⟨128,690877759,690878173⟩]
theorem checked18977 : checkPrefixCuts (2^48) 2491285505 9 Manual.Count131072.C018977.packed 128 cuts18977 = true := by
 decide +kernel
def pointBounds18977 : List (Nat × Nat × Nat) := [(2491353088,99339902911991,99340282877970)]
theorem point_links_checked18977 : (cuts18977.take 1).map (fun c => (2491285505-1+2*2^9*c.k,99339545888041+c.lower,99339925853806+c.upper)) = pointBounds18977 := by
 decide +kernel
def cuts18978 : List PrefixCut := [⟨15,81343798,81343845⟩,
⟨92,489523865,489524163⟩,
⟨128,682594285,682594700⟩]
theorem checked18978 : checkPrefixCuts (2^48) 2491416577 9 Manual.Count131072.C018978.packed 128 cuts18978 = true := by
 decide +kernel
def pointBounds18978 : List (Nat × Nat × Nat) := [(2491431936,99340318109598,99340698075824),(2491510784,99340726289665,99341106256142)]
theorem point_links_checked18978 : (cuts18978.take 2).map (fun c => (2491416577-1+2*2^9*c.k,99340236765800+c.lower,99340616731979+c.upper)) = pointBounds18978 := by
 decide +kernel
def cuts18979 : List PrefixCut := [⟨41,221310096,221310224⟩,
⟨118,633869989,633870358⟩,
⟨128,684139945,684140345⟩]
theorem checked18979 : checkPrefixCuts (2^48) 2491547649 9 Manual.Count131072.C018979.packed 128 cuts18979 = true := by
 decide +kernel
def pointBounds18979 : List (Nat × Nat × Nat) := [(2491589632,99341140670181,99341520636903),(2491668480,99341553230074,99341933197037)]
theorem point_links_checked18979 : (cuts18979.take 2).map (fun c => (2491547649-1+2*2^9*c.k,99340919360085+c.lower,99341299326679+c.upper)) = pointBounds18979 := by
 decide +kernel
def cuts18980 : List PrefixCut := [⟨67,359565699,359565915⟩,
⟨128,685798317,685798727⟩]
theorem checked18980 : checkPrefixCuts (2^48) 2491678721 9 Manual.Count131072.C018980.packed 128 cuts18980 = true := by
 decide +kernel
def pointBounds18980 : List (Nat × Nat × Nat) := [(2491747328,99341963065729,99342343032939)]
theorem point_links_checked18980 : (cuts18980.take 1).map (fun c => (2491678721-1+2*2^9*c.k,99341603500030+c.lower,99341983467024+c.upper)) = pointBounds18980 := by
 decide +kernel
def cuts18981 : List PrefixCut := [⟨16,84380856,84380906⟩,
⟨93,496788634,496788931⟩,
⟨128,683954930,683955339⟩]
theorem checked18981 : checkPrefixCuts (2^48) 2491809793 9 Manual.Count131072.C018981.packed 128 cuts18981 = true := by
 decide +kernel
def pointBounds18981 : List (Nat × Nat × Nat) := [(2491826176,99342373679203,99342753646657),(2491905024,99342786086981,99343166054682)]
theorem point_links_checked18981 : (cuts18981.take 2).map (fun c => (2491809793-1+2*2^9*c.k,99342289298347+c.lower,99342669265751+c.upper)) = pointBounds18981 := by
 decide +kernel
def cuts18982 : List PrefixCut := [⟨42,225567337,225567471⟩,
⟨119,635802991,635803369⟩,
⟨128,684144885,684145291⟩]
theorem checked18982 : checkPrefixCuts (2^48) 2491940865 9 Manual.Count131072.C018982.packed 128 cuts18982 = true := by
 decide +kernel
def pointBounds18982 : List (Nat × Nat × Nat) := [(2491983872,99343198820614,99343578788561),(2492062720,99343609056268,99343989024459)]
theorem point_links_checked18982 : (cuts18982.take 2).map (fun c => (2491940865-1+2*2^9*c.k,99342973253277+c.lower,99343353221090+c.upper)) = pointBounds18982 := by
 decide +kernel
def cuts18983 : List PrefixCut := [⟨68,358944186,358944407⟩,
⟨128,677106319,677106735⟩]
theorem checked18983 : checkPrefixCuts (2^48) 2492071937 9 Manual.Count131072.C018983.packed 128 cuts18983 = true := by
 decide +kernel
def pointBounds18983 : List (Nat × Nat × Nat) := [(2492141568,99344016342348,99344396310788)]
theorem point_links_checked18983 : (cuts18983.take 1).map (fun c => (2492071937-1+2*2^9*c.k,99343657398162+c.lower,99344037366381+c.upper)) = pointBounds18983 := by
 decide +kernel
def cuts18984 : List PrefixCut := [⟨17,87981668,87981717⟩,
⟨94,492870341,492870629⟩,
⟨128,673117891,673118286⟩]
theorem checked18984 : checkPrefixCuts (2^48) 2492203009 9 Manual.Count131072.C018984.packed 128 cuts18984 = true := by
 decide +kernel
def pointBounds18984 : List (Nat × Nat × Nat) := [(2492220416,99344422486149,99344802454833),(2492299264,99344827374822,99345207343745)]
theorem point_links_checked18984 : (cuts18984.take 2).map (fun c => (2492203009-1+2*2^9*c.k,99344334504481+c.lower,99344714473116+c.upper)) = pointBounds18984 := by
 decide +kernel
def cuts18985 : List PrefixCut := [⟨43,233776006,233776145⟩,
⟨120,646544255,646544637⟩,
⟨128,689231990,689232398⟩]
theorem checked18985 : checkPrefixCuts (2^48) 2492334081 9 Manual.Count131072.C018985.packed 128 cuts18985 = true := by
 decide +kernel
def pointBounds18985 : List (Nat × Nat × Nat) := [(2492378112,99345241398378,99345621367547),(2492456960,99345654166627,99346034136039)]
theorem point_links_checked18985 : (cuts18985.take 2).map (fun c => (2492334081-1+2*2^9*c.k,99345007622372+c.lower,99345387591402+c.upper)) = pointBounds18985 := by
 decide +kernel
def cuts18986 : List PrefixCut := [⟨69,371535531,371535749⟩,
⟨128,687953502,687953908⟩]
theorem checked18986 : checkPrefixCuts (2^48) 2492465153 9 Manual.Count131072.C018986.packed 128 cuts18986 = true := by
 decide +kernel
def pointBounds18986 : List (Nat × Nat × Nat) := [(2492535808,99346068389893,99346448359549)]
theorem point_links_checked18986 : (cuts18986.take 1).map (fun c => (2492465153-1+2*2^9*c.k,99345696854362+c.lower,99346076823800+c.upper)) = pointBounds18986 := by
 decide +kernel
def cuts18987 : List PrefixCut := [⟨18,95759517,95759576⟩,
⟨95,509617791,509618092⟩,
⟨128,692659828,692660234⟩]
theorem checked18987 : checkPrefixCuts (2^48) 2492596225 9 Manual.Count131072.C018987.packed 128 cuts18987 = true := by
 decide +kernel
def pointBounds18987 : List (Nat × Nat × Nat) := [(2492614656,99346480567381,99346860537284),(2492693504,99346894425655,99347274395800)]
theorem point_links_checked18987 : (cuts18987.take 2).map (fun c => (2492596225-1+2*2^9*c.k,99346384807864+c.lower,99346764777708+c.upper)) = pointBounds18987 := by
 decide +kernel
def cuts18988 : List PrefixCut := [⟨44,230690318,230690459⟩,
⟨121,642489956,642490340⟩,
⟨128,678847837,678848243⟩]
theorem checked18988 : checkPrefixCuts (2^48) 2492727297 9 Manual.Count131072.C018988.packed 128 cuts18988 = true := by
 decide +kernel
def pointBounds18988 : List (Nat × Nat × Nat) := [(2492772352,99347308158010,99347688128401),(2492851200,99347719957648,99348099928282)]
theorem point_links_checked18988 : (cuts18988.take 2).map (fun c => (2492727297-1+2*2^9*c.k,99347077467692+c.lower,99347457437942+c.upper)) = pointBounds18988 := by
 decide +kernel
def cuts18989 : List PrefixCut := [⟨70,379832251,379832473⟩,
⟨128,679038270,679038669⟩]
theorem checked18989 : checkPrefixCuts (2^48) 2492858369 9 Manual.Count131072.C018989.packed 128 cuts18989 = true := by
 decide +kernel
def pointBounds18989 : List (Nat × Nat × Nat) := [(2492930048,99348136147780,99348516118658)]
theorem point_links_checked18989 : (cuts18989.take 1).map (fun c => (2492858369-1+2*2^9*c.k,99347756315529+c.lower,99348136286185+c.upper)) = pointBounds18989 := by
 decide +kernel
def cuts18990 : List PrefixCut := [⟨19,102970386,102970447⟩,
⟨96,514166374,514166682⟩,
⟨128,685889369,685889781⟩]
theorem checked18990 : checkPrefixCuts (2^48) 2492989441 9 Manual.Count131072.C018990.packed 128 cuts18990 = true := by
 decide +kernel
def pointBounds18990 : List (Nat × Nat × Nat) := [(2493008896,99348538324185,99348918295301),(2493087744,99348949520173,99349329491536)]
theorem point_links_checked18990 : (cuts18990.take 2).map (fun c => (2492989441-1+2*2^9*c.k,99348435353799+c.lower,99348815324854+c.upper)) = pointBounds18990 := by
 decide +kernel
def cuts18991 : List PrefixCut := [⟨45,238331034,238331175⟩,
⟨122,651194471,651194852⟩,
⟨128,685401607,685402007⟩]
theorem checked18991 : checkPrefixCuts (2^48) 2493120513 9 Manual.Count131072.C018991.packed 128 cuts18991 = true := by
 decide +kernel
def pointBounds18991 : List (Nat × Nat × Nat) := [(2493166592,99349359574202,99349739545810),(2493245440,99349772437639,99350152409487)]
theorem point_links_checked18991 : (cuts18991.take 2).map (fun c => (2493120513-1+2*2^9*c.k,99349121243168+c.lower,99349501214635+c.upper)) = pointBounds18991 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000280
