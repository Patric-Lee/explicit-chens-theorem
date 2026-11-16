import PlattAssemblyKernel
import PlattCertificates.Count131072.C019856
import PlattCertificates.Count131072.C019857
import PlattCertificates.Count131072.C019858
import PlattCertificates.Count131072.C019859
import PlattCertificates.Count131072.C019860
import PlattCertificates.Count131072.C019861
import PlattCertificates.Count131072.C019862
import PlattCertificates.Count131072.C019863
import PlattCertificates.Count131072.C019864
import PlattCertificates.Count131072.C019865
import PlattCertificates.Count131072.C019866
import PlattCertificates.Count131072.C019867
import PlattCertificates.Count131072.C019868
import PlattCertificates.Count131072.C019869
import PlattCertificates.Count131072.C019870
import PlattCertificates.Count131072.C019871
import PlattCertificates.Count131072.C019872
import PlattCertificates.Count131072.C019873
import PlattCertificates.Count131072.C019874
import PlattCertificates.Count131072.C019875
import PlattCertificates.Count131072.C019876
import PlattCertificates.Count131072.C019877
import PlattCertificates.Count131072.C019878
import PlattCertificates.Count131072.C019879
import PlattCertificates.Count131072.C019880
import PlattCertificates.Count131072.C019881
import PlattCertificates.Count131072.C019882
import PlattCertificates.Count131072.C019883
import PlattCertificates.Count131072.C019884
import PlattCertificates.Count131072.C019885
import PlattCertificates.Count131072.C019886
import PlattCertificates.Count131072.C019887
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000308
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts19856 : List PrefixCut := [⟨77,390916800,390917030⟩,
⟨128,650189610,650189988⟩]
theorem checked19856 : checkPrefixCuts (2^48) 2606497793 9 Manual.Count131072.C019856.packed 128 cuts19856 = true := by
 decide +kernel
def pointBounds19856 : List (Nat × Nat × Nat) := [(2606576640,99927629916922,99928010231828)]
theorem point_links_checked19856 : (cuts19856.take 1).map (fun c => (2606497793-1+2*2^9*c.k,99927239000122+c.lower,99927619314798+c.upper)) = pointBounds19856 := by
 decide +kernel
def cuts19857 : List PrefixCut := [⟨29,145669934,145670019⟩,
⟨109,552219638,552219965⟩,
⟨128,649832865,649833248⟩]
theorem checked19857 : checkPrefixCuts (2^48) 2606628865 9 Manual.Count131072.C019857.packed 128 cuts19857 = true := by
 decide +kernel
def pointBounds19857 : List (Nat × Nat × Nat) := [(2606658560,99928034859666,99928415174805),(2606740480,99928441409370,99928821724751)]
theorem point_links_checked19857 : (cuts19857.take 2).map (fun c => (2606628865-1+2*2^9*c.k,99927889189732+c.lower,99928269504786+c.upper)) = pointBounds19857 := by
 decide +kernel
def cuts19858 : List PrefixCut := [⟨61,313566744,313566928⟩,
⟨128,658330258,658330647⟩]
theorem checked19858 : checkPrefixCuts (2^48) 2606759937 9 Manual.Count131072.C019858.packed 128 cuts19858 = true := by
 decide +kernel
def pointBounds19858 : List (Nat × Nat × Nat) := [(2606822400,99928852589341,99929232904962)]
theorem point_links_checked19858 : (cuts19858.take 1).map (fun c => (2606759937-1+2*2^9*c.k,99928539022597+c.lower,99928919338034+c.upper)) = pointBounds19858 := by
 decide +kernel
def cuts19859 : List PrefixCut := [⟨13,66295504,66295543⟩,
⟨93,474858430,474858713⟩,
⟨128,650631520,650631904⟩]
theorem checked19859 : checkPrefixCuts (2^48) 2606891009 9 Manual.Count131072.C019859.packed 128 cuts19859 = true := by
 decide +kernel
def pointBounds19859 : List (Nat × Nat × Nat) := [(2606904320,99929263648359,99929643964224),(2606986240,99929672211285,99930052527394)]
theorem point_links_checked19859 : (cuts19859.take 2).map (fun c => (2606891009-1+2*2^9*c.k,99929197352855+c.lower,99929577668681+c.upper)) = pointBounds19859 := by
 decide +kernel
def cuts19860 : List PrefixCut := [⟨45,229861773,229861910⟩,
⟨125,634404300,634404678⟩,
⟨128,647791663,647792049⟩]
theorem checked19860 : checkPrefixCuts (2^48) 2607022081 9 Manual.Count131072.C019860.packed 128 cuts19860 = true := by
 decide +kernel
def pointBounds19860 : List (Nat × Nat × Nat) := [(2607068160,99930077846148,99930458162495),(2607150080,99930482388675,99930862705263)]
theorem point_links_checked19860 : (cuts19860.take 2).map (fun c => (2607022081-1+2*2^9*c.k,99929847984375+c.lower,99930228300585+c.upper)) = pointBounds19860 := by
 decide +kernel
def cuts19861 : List PrefixCut := [⟨77,390602525,390602758⟩,
⟨128,651537485,651537872⟩]
theorem checked19861 : checkPrefixCuts (2^48) 2607153153 9 Manual.Count131072.C019861.packed 128 cuts19861 = true := by
 decide +kernel
def pointBounds19861 : List (Nat × Nat × Nat) := [(2607232000,99930886378563,99931266695392)]
theorem point_links_checked19861 : (cuts19861.take 1).map (fun c => (2607153153-1+2*2^9*c.k,99930495776038+c.lower,99930876092634+c.upper)) = pointBounds19861 := by
 decide +kernel
def cuts19862 : List PrefixCut := [⟨29,145849241,145849328⟩,
⟨109,557802406,557802732⟩,
⟨128,650857096,650857481⟩]
theorem checked19862 : checkPrefixCuts (2^48) 2607284225 9 Manual.Count131072.C019862.packed 128 cuts19862 = true := by
 decide +kernel
def pointBounds19862 : List (Nat × Nat × Nat) := [(2607313920,99931293162764,99931673479834),(2607395840,99931705115929,99932085433238)]
theorem point_links_checked19862 : (cuts19862.take 2).map (fun c => (2607284225-1+2*2^9*c.k,99931147313523+c.lower,99931527630506+c.upper)) = pointBounds19862 := by
 decide +kernel
def cuts19863 : List PrefixCut := [⟨61,303340622,303340802⟩,
⟨128,646938081,646938462⟩]
theorem checked19863 : checkPrefixCuts (2^48) 2607415297 9 Manual.Count131072.C019863.packed 128 cuts19863 = true := by
 decide +kernel
def pointBounds19863 : List (Nat × Nat × Nat) := [(2607477760,99932101511241,99932481828789)]
theorem point_links_checked19863 : (cuts19863.take 1).map (fun c => (2607415297-1+2*2^9*c.k,99931798170619+c.lower,99932178487987+c.upper)) = pointBounds19863 := by
 decide +kernel
def cuts19864 : List PrefixCut := [⟨13,64767593,64767633⟩,
⟨93,468478247,468478528⟩,
⟨128,647661284,647661667⟩]
theorem checked19864 : checkPrefixCuts (2^48) 2607546369 9 Manual.Count131072.C019864.packed 128 cuts19864 = true := by
 decide +kernel
def pointBounds19864 : List (Nat × Nat × Nat) := [(2607559680,99932509876293,99932890194082),(2607641600,99932913586947,99933293904977)]
theorem point_links_checked19864 : (cuts19864.take 2).map (fun c => (2607546369-1+2*2^9*c.k,99932445108700+c.lower,99932825426449+c.upper)) = pointBounds19864 := by
 decide +kernel
def cuts19865 : List PrefixCut := [⟨45,223543510,223543644⟩,
⟨125,634028819,634029196⟩,
⟨128,649571527,649571914⟩]
theorem checked19865 : checkPrefixCuts (2^48) 2607677441 9 Manual.Count131072.C019865.packed 128 cuts19865 = true := by
 decide +kernel
def pointBounds19865 : List (Nat × Nat × Nat) := [(2607723520,99933316313494,99933696631760),(2607805440,99933726798803,99934107117312)]
theorem point_links_checked19865 : (cuts19865.take 2).map (fun c => (2607677441-1+2*2^9*c.k,99933092769984+c.lower,99933473088116+c.upper)) = pointBounds19865 := by
 decide +kernel
def cuts19866 : List PrefixCut := [⟨77,395037631,395037860⟩,
⟨128,656122901,656123283⟩]
theorem checked19866 : checkPrefixCuts (2^48) 2607808513 9 Manual.Count131072.C019866.packed 128 cuts19866 = true := by
 decide +kernel
def pointBounds19866 : List (Nat × Nat × Nat) := [(2607887360,99934137379142,99934517697890)]
theorem point_links_checked19866 : (cuts19866.take 1).map (fun c => (2607808513-1+2*2^9*c.k,99933742341511+c.lower,99934122660030+c.upper)) = pointBounds19866 := by
 decide +kernel
def cuts19867 : List PrefixCut := [⟨29,149698052,149698142⟩,
⟨109,555287923,555288251⟩,
⟨128,652960025,652960413⟩]
theorem checked19867 : checkPrefixCuts (2^48) 2607939585 9 Manual.Count131072.C019867.packed 128 cuts19867 = true := by
 decide +kernel
def pointBounds19867 : List (Nat × Nat × Nat) := [(2607969280,99934548162464,99934928481455),(2608051200,99934953752335,99935334071564)]
theorem point_links_checked19867 : (cuts19867.take 2).map (fun c => (2607939585-1+2*2^9*c.k,99934398464412+c.lower,99934778783313+c.upper)) = pointBounds19867 := by
 decide +kernel
def cuts19868 : List PrefixCut := [⟨61,312329962,312330144⟩,
⟨128,648070836,648071223⟩]
theorem checked19868 : checkPrefixCuts (2^48) 2608070657 9 Manual.Count131072.C019868.packed 128 cuts19868 = true := by
 decide +kernel
def pointBounds19868 : List (Nat × Nat × Nat) := [(2608133120,99935363754399,99935744073870)]
theorem point_links_checked19868 : (cuts19868.take 1).map (fun c => (2608070657-1+2*2^9*c.k,99935051424437+c.lower,99935431743726+c.upper)) = pointBounds19868 := by
 decide +kernel
def cuts19869 : List PrefixCut := [⟨13,66693860,66693899⟩,
⟨93,476454285,476454565⟩,
⟨128,654944817,654945204⟩]
theorem checked19869 : checkPrefixCuts (2^48) 2608201729 9 Manual.Count131072.C019869.packed 128 cuts19869 = true := by
 decide +kernel
def pointBounds19869 : List (Nat × Nat × Nat) := [(2608215040,99935766189133,99936146508848),(2608296960,99936175949558,99936556269514)]
theorem point_links_checked19869 : (cuts19869.take 2).map (fun c => (2608201729-1+2*2^9*c.k,99935699495273+c.lower,99936079814949+c.upper)) = pointBounds19869 := by
 decide +kernel
def cuts19870 : List PrefixCut := [⟨45,232012452,232012590⟩,
⟨125,635812135,635812512⟩,
⟨128,651458848,651459234⟩]
theorem checked19870 : checkPrefixCuts (2^48) 2608332801 9 Manual.Count131072.C019870.packed 128 cuts19870 = true := by
 decide +kernel
def pointBounds19870 : List (Nat × Nat × Nat) := [(2608378880,99936586452542,99936966772743),(2608460800,99936990252225,99937370572665)]
theorem point_links_checked19870 : (cuts19870.take 2).map (fun c => (2608332801-1+2*2^9*c.k,99936354440090+c.lower,99936734760153+c.upper)) = pointBounds19870 := by
 decide +kernel
def cuts19871 : List PrefixCut := [⟨77,383716144,383716372⟩,
⟨128,650562597,650562979⟩]
theorem checked19871 : checkPrefixCuts (2^48) 2608463873 9 Manual.Count131072.C019871.packed 128 cuts19871 = true := by
 decide +kernel
def pointBounds19871 : List (Nat × Nat × Nat) := [(2608542720,99937389615082,99937769935759)]
theorem point_links_checked19871 : (cuts19871.take 1).map (fun c => (2608463873-1+2*2^9*c.k,99937005898938+c.lower,99937386219387+c.upper)) = pointBounds19871 := by
 decide +kernel
def cuts19872 : List PrefixCut := [⟨29,144373219,144373305⟩,
⟨109,552666649,552666977⟩,
⟨128,649882619,649883004⟩]
theorem checked19872 : checkPrefixCuts (2^48) 2608594945 9 Manual.Count131072.C019872.packed 128 cuts19872 = true := by
 decide +kernel
def pointBounds19872 : List (Nat × Nat × Nat) := [(2608624640,99937800834754,99938181155671),(2608706560,99938209128184,99938589449343)]
theorem point_links_checked19872 : (cuts19872.take 2).map (fun c => (2608594945-1+2*2^9*c.k,99937656461535+c.lower,99938036782366+c.upper)) = pointBounds19872 := by
 decide +kernel
def cuts19873 : List PrefixCut := [⟨61,318293643,318293825⟩,
⟨128,656755424,656755802⟩]
theorem checked19873 : checkPrefixCuts (2^48) 2608726017 9 Manual.Count131072.C019873.packed 128 cuts19873 = true := by
 decide +kernel
def pointBounds19873 : List (Nat × Nat × Nat) := [(2608788480,99938624637797,99939004959195)]
theorem point_links_checked19873 : (cuts19873.take 1).map (fun c => (2608726017-1+2*2^9*c.k,99938306344154+c.lower,99938686665370+c.upper)) = pointBounds19873 := by
 decide +kernel
def cuts19874 : List PrefixCut := [⟨13,67324461,67324501⟩,
⟨93,473421617,473421895⟩,
⟨128,652730384,652730766⟩]
theorem checked19874 : checkPrefixCuts (2^48) 2608857089 9 Manual.Count131072.C019874.packed 128 cuts19874 = true := by
 decide +kernel
def pointBounds19874 : List (Nat × Nat × Nat) := [(2608870400,99939030424039,99939410745673),(2608952320,99939436521195,99939816843067)]
theorem point_links_checked19874 : (cuts19874.take 2).map (fun c => (2608857089-1+2*2^9*c.k,99938963099578+c.lower,99939343421172+c.upper)) = pointBounds19874 := by
 decide +kernel
def cuts19875 : List PrefixCut := [⟨45,231846247,231846382⟩,
⟨125,636731230,636731601⟩,
⟨128,651618843,651619224⟩]
theorem checked19875 : checkPrefixCuts (2^48) 2608988161 9 Manual.Count131072.C019875.packed 128 cuts19875 = true := by
 decide +kernel
def pointBounds19875 : List (Nat × Nat × Nat) := [(2609034240,99939847676209,99940227998320),(2609116160,99940252561192,99940632883539)]
theorem point_links_checked19875 : (cuts19875.take 2).map (fun c => (2608988161-1+2*2^9*c.k,99939615829962+c.lower,99939996151938+c.upper)) = pointBounds19875 := by
 decide +kernel
def cuts19876 : List PrefixCut := [⟨77,391710705,391710935⟩,
⟨128,650938770,650939155⟩]
theorem checked19876 : checkPrefixCuts (2^48) 2609119233 9 Manual.Count131072.C019876.packed 128 cuts19876 = true := by
 decide +kernel
def pointBounds19876 : List (Nat × Nat × Nat) := [(2609198080,99940659159510,99941039482097)]
theorem point_links_checked19876 : (cuts19876.take 1).map (fun c => (2609119233-1+2*2^9*c.k,99940267448805+c.lower,99940647771162+c.upper)) = pointBounds19876 := by
 decide +kernel
def cuts19877 : List PrefixCut := [⟨29,148220462,148220552⟩,
⟨109,555871873,555872205⟩,
⟨128,649719433,649719821⟩]
theorem checked19877 : checkPrefixCuts (2^48) 2609250305 9 Manual.Count131072.C019877.packed 128 cuts19877 = true := by
 decide +kernel
def pointBounds19877 : List (Nat × Nat × Nat) := [(2609280000,99941066608037,99941446930869),(2609361920,99941474259448,99941854582522)]
theorem point_links_checked19877 : (cuts19877.take 2).map (fun c => (2609250305-1+2*2^9*c.k,99940918387575+c.lower,99941298710317+c.upper)) = pointBounds19877 := by
 decide +kernel
def cuts19878 : List PrefixCut := [⟨61,309584223,309584407⟩,
⟨128,645803678,645804062⟩]
theorem checked19878 : checkPrefixCuts (2^48) 2609381377 9 Manual.Count131072.C019878.packed 128 cuts19878 = true := by
 decide +kernel
def pointBounds19878 : List (Nat × Nat × Nat) := [(2609443840,99941877691231,99942258014545)]
theorem point_links_checked19878 : (cuts19878.take 1).map (fun c => (2609381377-1+2*2^9*c.k,99941568107008+c.lower,99941948430138+c.upper)) = pointBounds19878 := by
 decide +kernel
def cuts19879 : List PrefixCut := [⟨13,67307547,67307586⟩,
⟨93,474273463,474273741⟩,
⟨128,655478691,655479076⟩]
theorem checked19879 : checkPrefixCuts (2^48) 2609512449 9 Manual.Count131072.C019879.packed 128 cuts19879 = true := by
 decide +kernel
def pointBounds19879 : List (Nat × Nat × Nat) := [(2609525760,99942281218233,99942661541786),(2609607680,99942688184149,99943068507941)]
theorem point_links_checked19879 : (cuts19879.take 2).map (fun c => (2609512449-1+2*2^9*c.k,99942213910686+c.lower,99942594234200+c.upper)) = pointBounds19879 := by
 decide +kernel
def cuts19880 : List PrefixCut := [⟨45,221649315,221649447⟩,
⟨125,626216891,626217266⟩,
⟨128,642502870,642503254⟩]
theorem checked19880 : checkPrefixCuts (2^48) 2609643521 9 Manual.Count131072.C019880.packed 128 cuts19880 = true := by
 decide +kernel
def pointBounds19880 : List (Nat × Nat × Nat) := [(2609689600,99943091038692,99943471362723),(2609771520,99943495606268,99943875930542)]
theorem point_links_checked19880 : (cuts19880.take 2).map (fun c => (2609643521-1+2*2^9*c.k,99942869389377+c.lower,99943249713276+c.upper)) = pointBounds19880 := by
 decide +kernel
def cuts19881 : List PrefixCut := [⟨77,395494999,395495228⟩,
⟨128,646461362,646461743⟩]
theorem checked19881 : checkPrefixCuts (2^48) 2609774593 9 Manual.Count131072.C019881.packed 128 cuts19881 = true := by
 decide +kernel
def pointBounds19881 : List (Nat × Nat × Nat) := [(2609853440,99943907387246,99944287711758)]
theorem point_links_checked19881 : (cuts19881.take 1).map (fun c => (2609774593-1+2*2^9*c.k,99943511892247+c.lower,99943892216530+c.upper)) = pointBounds19881 := by
 decide +kernel
def cuts19882 : List PrefixCut := [⟨29,150879454,150879541⟩,
⟨109,562095404,562095733⟩,
⟨128,659693927,659694312⟩]
theorem checked19882 : checkPrefixCuts (2^48) 2609905665 9 Manual.Count131072.C019882.packed 128 cuts19882 = true := by
 decide +kernel
def pointBounds19882 : List (Nat × Nat × Nat) := [(2609935360,99944309233063,99944689557814),(2610017280,99944720449013,99945100774006)]
theorem point_links_checked19882 : (cuts19882.take 2).map (fun c => (2609905665-1+2*2^9*c.k,99944158353609+c.lower,99944538678273+c.upper)) = pointBounds19882 := by
 decide +kernel
def cuts19883 : List PrefixCut := [⟨61,314143673,314143859⟩,
⟨128,659552817,659553204⟩]
theorem checked19883 : checkPrefixCuts (2^48) 2610036737 9 Manual.Count131072.C019883.packed 128 cuts19883 = true := by
 decide +kernel
def pointBounds19883 : List (Nat × Nat × Nat) := [(2610099200,99945132191209,99945512516444)]
theorem point_links_checked19883 : (cuts19883.take 1).map (fun c => (2610036737-1+2*2^9*c.k,99944818047536+c.lower,99945198372585+c.upper)) = pointBounds19883 := by
 decide +kernel
def cuts19884 : List PrefixCut := [⟨13,67614161,67614201⟩,
⟨93,474801409,474801686⟩,
⟨128,652726153,652726535⟩]
theorem checked19884 : checkPrefixCuts (2^48) 2610167809 9 Manual.Count131072.C019884.packed 128 cuts19884 = true := by
 decide +kernel
def pointBounds19884 : List (Nat × Nat × Nat) := [(2610181120,99945545214514,99945925539990),(2610263040,99945952401762,99946332727475)]
theorem point_links_checked19884 : (cuts19884.take 2).map (fun c => (2610167809-1+2*2^9*c.k,99945477600353+c.lower,99945857925789+c.upper)) = pointBounds19884 := by
 decide +kernel
def cuts19885 : List PrefixCut := [⟨45,231945540,231945677⟩,
⟨125,641910811,641911190⟩,
⟨128,659055318,659055707⟩]
theorem checked19885 : checkPrefixCuts (2^48) 2610298881 9 Manual.Count131072.C019885.packed 128 cuts19885 = true := by
 decide +kernel
def pointBounds19885 : List (Nat × Nat × Nat) := [(2610344960,99946362272046,99946742598001),(2610426880,99946772237317,99947152563514)]
theorem point_links_checked19885 : (cuts19885.take 2).map (fun c => (2610298881-1+2*2^9*c.k,99946130326506+c.lower,99946510652324+c.upper)) = pointBounds19885 := by
 decide +kernel
def cuts19886 : List PrefixCut := [⟨77,385799297,385799528⟩,
⟨128,646406730,646407118⟩]
theorem checked19886 : checkPrefixCuts (2^48) 2610429953 9 Manual.Count131072.C019886.packed 128 cuts19886 = true := by
 decide +kernel
def pointBounds19886 : List (Nat × Nat × Nat) := [(2610508800,99947175181121,99947555507559)]
theorem point_links_checked19886 : (cuts19886.take 1).map (fun c => (2610429953-1+2*2^9*c.k,99946789381824+c.lower,99947169708031+c.upper)) = pointBounds19886 := by
 decide +kernel
def cuts19887 : List PrefixCut := [⟨29,150302472,150302565⟩,
⟨109,553544417,553544751⟩,
⟨128,650363721,650364114⟩]
theorem checked19887 : checkPrefixCuts (2^48) 2610561025 9 Manual.Count131072.C019887.packed 128 cuts19887 = true := by
 decide +kernel
def pointBounds19887 : List (Nat × Nat × Nat) := [(2610590720,99947586091026,99947966417714),(2610672640,99947989332971,99948369659900)]
theorem point_links_checked19887 : (cuts19887.take 2).map (fun c => (2610561025-1+2*2^9*c.k,99947435788554+c.lower,99947816115149+c.upper)) = pointBounds19887 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000308
