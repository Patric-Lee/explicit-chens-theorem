import PlattAssemblyKernel
import PlattCertificates.Count131072.C020864
import PlattCertificates.Count131072.C020865
import PlattCertificates.Count131072.C020866
import PlattCertificates.Count131072.C020867
import PlattCertificates.Count131072.C020868
import PlattCertificates.Count131072.C020869
import PlattCertificates.Count131072.C020870
import PlattCertificates.Count131072.C020871
import PlattCertificates.Count131072.C020872
import PlattCertificates.Count131072.C020873
import PlattCertificates.Count131072.C020874
import PlattCertificates.Count131072.C020875
import PlattCertificates.Count131072.C020876
import PlattCertificates.Count131072.C020877
import PlattCertificates.Count131072.C020878
import PlattCertificates.Count131072.C020879
import PlattCertificates.Count131072.C020880
import PlattCertificates.Count131072.C020881
import PlattCertificates.Count131072.C020882
import PlattCertificates.Count131072.C020883
import PlattCertificates.Count131072.C020884
import PlattCertificates.Count131072.C020885
import PlattCertificates.Count131072.C020886
import PlattCertificates.Count131072.C020887
import PlattCertificates.Count131072.C020888
import PlattCertificates.Count131072.C020889
import PlattCertificates.Count131072.C020890
import PlattCertificates.Count131072.C020891
import PlattCertificates.Count131072.C020892
import PlattCertificates.Count131072.C020893
import PlattCertificates.Count131072.C020894
import PlattCertificates.Count131072.C020895
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000027
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts20864 : List PrefixCut := [⟨21,99387763,99387821⟩,
⟨105,500733817,500734103⟩,
⟨128,609778529,609778879⟩]
theorem checked20864 : checkPrefixCuts (2^48) 2738618369 9 Manual.Count131072.C020864.packed 128 cuts20864 = true := by
 decide +kernel
def pointBounds20864 : List (Nat × Nat × Nat) := [(2738639872,100568419872075,100568800561658),(2738725888,100568821218129,100569201907940)]
theorem point_links_checked20864 : (cuts20864.take 2).map (fun c => (2738618369-1+2*2^9*c.k,100568320484312+c.lower,100568701173837+c.upper)) = pointBounds20864 := by
 decide +kernel
def cuts20865 : List PrefixCut := [⟨61,298455091,298455264⟩,
⟨128,629584353,629584713⟩]
theorem checked20865 : checkPrefixCuts (2^48) 2738749441 9 Manual.Count131072.C020865.packed 128 cuts20865 = true := by
 decide +kernel
def pointBounds20865 : List (Nat × Nat × Nat) := [(2738811904,100569228717932,100569609407980)]
theorem point_links_checked20865 : (cuts20865.take 1).map (fun c => (2738749441-1+2*2^9*c.k,100568930262841+c.lower,100569310952716+c.upper)) = pointBounds20865 := by
 decide +kernel
def cuts20866 : List PrefixCut := [⟨17,80674240,80674289⟩,
⟨101,491848125,491848415⟩,
⟨128,626060087,626060454⟩]
theorem checked20866 : checkPrefixCuts (2^48) 2738880513 9 Manual.Count131072.C020866.packed 128 cuts20866 = true := by
 decide +kernel
def pointBounds20866 : List (Nat × Nat × Nat) := [(2738897920,100569640521434,100570021211718),(2738983936,100570051695319,100570432385844)]
theorem point_links_checked20866 : (cuts20866.take 2).map (fun c => (2738880513-1+2*2^9*c.k,100569559847194+c.lower,100569940537429+c.upper)) = pointBounds20866 := by
 decide +kernel
def cuts20867 : List PrefixCut := [⟨57,277873947,277874109⟩,
⟨128,625413654,625414019⟩]
theorem checked20867 : checkPrefixCuts (2^48) 2739011585 9 Manual.Count131072.C020867.packed 128 cuts20867 = true := by
 decide +kernel
def pointBounds20867 : List (Nat × Nat × Nat) := [(2739069952,100570463781228,100570844471992)]
theorem point_links_checked20867 : (cuts20867.take 1).map (fun c => (2739011585-1+2*2^9*c.k,100570185907281+c.lower,100570566597883+c.upper)) = pointBounds20867 := by
 decide +kernel
def cuts20868 : List PrefixCut := [⟨13,65047058,65047094⟩,
⟨97,468064368,468064630⟩,
⟨128,622917499,622917852⟩]
theorem checked20868 : checkPrefixCuts (2^48) 2739142657 9 Manual.Count131072.C020868.packed 128 cuts20868 = true := by
 decide +kernel
def pointBounds20868 : List (Nat × Nat × Nat) := [(2739155968,100570876367993,100571257058996),(2739241984,100571279385303,100571660076532)]
theorem point_links_checked20868 : (cuts20868.take 2).map (fun c => (2739142657-1+2*2^9*c.k,100570811320935+c.lower,100571192011902+c.upper)) = pointBounds20868 := by
 decide +kernel
def cuts20869 : List PrefixCut := [⟨53,255858171,255858319⟩,
⟨128,618983105,618983467⟩]
theorem checked20869 : checkPrefixCuts (2^48) 2739273729 9 Manual.Count131072.C020869.packed 128 cuts20869 = true := by
 decide +kernel
def pointBounds20869 : List (Nat × Nat × Nat) := [(2739328000,100571690096605,100572070788073)]
theorem point_links_checked20869 : (cuts20869.take 1).map (fun c => (2739273729-1+2*2^9*c.k,100571434238434+c.lower,100571814929754+c.upper)) = pointBounds20869 := by
 decide +kernel
def cuts20870 : List PrefixCut := [⟨9,46032094,46032120⟩,
⟨93,456100988,456101251⟩,
⟨128,627789791,627790151⟩]
theorem checked20870 : checkPrefixCuts (2^48) 2739404801 9 Manual.Count131072.C020870.packed 128 cuts20870 = true := by
 decide +kernel
def pointBounds20870 : List (Nat × Nat × Nat) := [(2739414016,100572099253633,100572479945341),(2739500032,100572509322527,100572890014472)]
theorem point_links_checked20870 : (cuts20870.take 2).map (fun c => (2739404801-1+2*2^9*c.k,100572053221539+c.lower,100572433913221+c.upper)) = pointBounds20870 := by
 decide +kernel
def cuts20871 : List PrefixCut := [⟨49,236723365,236723502⟩,
⟨128,616971766,616972124⟩]
theorem checked20871 : checkPrefixCuts (2^48) 2739535873 9 Manual.Count131072.C020871.packed 128 cuts20871 = true := by
 decide +kernel
def pointBounds20871 : List (Nat × Nat × Nat) := [(2739586048,100572917734695,100573298426874)]
theorem point_links_checked20871 : (cuts20871.take 1).map (fun c => (2739535873-1+2*2^9*c.k,100572681011330+c.lower,100573061703372+c.upper)) = pointBounds20871 := by
 decide +kernel
def cuts20872 : List PrefixCut := [⟨5,23116603,23116616⟩,
⟨89,424516904,424517153⟩,
⟨128,614373730,614374083⟩]
theorem checked20872 : checkPrefixCuts (2^48) 2739666945 9 Manual.Count131072.C020872.packed 128 cuts20872 = true := by
 decide +kernel
def pointBounds20872 : List (Nat × Nat × Nat) := [(2739672064,100573321099699,100573701792112),(2739758080,100573722500000,100574103192649)]
theorem point_links_checked20872 : (cuts20872.take 2).map (fun c => (2739666945-1+2*2^9*c.k,100573297983096+c.lower,100573678675496+c.upper)) = pointBounds20872 := by
 decide +kernel
def cuts20873 : List PrefixCut := [⟨45,218414131,218414257⟩,
⟨128,616399127,616399483⟩]
theorem checked20873 : checkPrefixCuts (2^48) 2739798017 9 Manual.Count131072.C020873.packed 128 cuts20873 = true := by
 decide +kernel
def pointBounds20873 : List (Nat × Nat × Nat) := [(2739844096,100574130770957,100574511463836)]
theorem point_links_checked20873 : (cuts20873.take 1).map (fun c => (2739798017-1+2*2^9*c.k,100573912356826+c.lower,100574293049579+c.upper)) = pointBounds20873 := by
 decide +kernel
def cuts20874 : List PrefixCut := [⟨1,5752919,5752923⟩,
⟨85,405985387,405985618⟩,
⟨128,613082293,613082648⟩]
theorem checked20874 : checkPrefixCuts (2^48) 2739929089 9 Manual.Count131072.C020874.packed 128 cuts20874 = true := by
 decide +kernel
def pointBounds20874 : List (Nat × Nat × Nat) := [(2739930112,100574534508872,100574915201985),(2740016128,100574934741340,100575315434680)]
theorem point_links_checked20874 : (cuts20874.take 2).map (fun c => (2739929089-1+2*2^9*c.k,100574528755953+c.lower,100574909449062+c.upper)) = pointBounds20874 := by
 decide +kernel
def cuts20875 : List PrefixCut := [⟨41,201032844,201032958⟩,
⟨125,606889965,606890309⟩,
⟨128,621168178,621168530⟩]
theorem checked20875 : checkPrefixCuts (2^48) 2740060161 9 Manual.Count131072.C020875.packed 128 cuts20875 = true := by
 decide +kernel
def pointBounds20875 : List (Nat × Nat × Nat) := [(2740102144,100575342871090,100575723564668),(2740188160,100575748728211,100576129422019)]
theorem point_links_checked20875 : (cuts20875.take 2).map (fun c => (2740060161-1+2*2^9*c.k,100575141838246+c.lower,100575522531710+c.upper)) = pointBounds20875 := by
 decide +kernel
def cuts20876 : List PrefixCut := [⟨81,393517776,393518007⟩,
⟨128,629766607,629766972⟩]
theorem checked20876 : checkPrefixCuts (2^48) 2740191233 9 Manual.Count131072.C020876.packed 128 cuts20876 = true := by
 decide +kernel
def pointBounds20876 : List (Nat × Nat × Nat) := [(2740274176,100576156524200,100576537218247)]
theorem point_links_checked20876 : (cuts20876.take 1).map (fun c => (2740191233-1+2*2^9*c.k,100575763006424+c.lower,100576143700240+c.upper)) = pointBounds20876 := by
 decide +kernel
def cuts20877 : List PrefixCut := [⟨37,177081112,177081218⟩,
⟨121,584954223,584954561⟩,
⟨128,619259766,619260123⟩]
theorem checked20877 : checkPrefixCuts (2^48) 2740322305 9 Manual.Count131072.C020877.packed 128 cuts20877 = true := by
 decide +kernel
def pointBounds20877 : List (Nat × Nat × Nat) := [(2740360192,100576569854143,100576950548430),(2740446208,100576977727254,100577358421773)]
theorem point_links_checked20877 : (cuts20877.take 2).map (fun c => (2740322305-1+2*2^9*c.k,100576392773031+c.lower,100576773467212+c.upper)) = pointBounds20877 := by
 decide +kernel
def cuts20878 : List PrefixCut := [⟨77,373349349,373349565⟩,
⟨128,618305891,618306249⟩]
theorem checked20878 : checkPrefixCuts (2^48) 2740453377 9 Manual.Count131072.C020878.packed 128 cuts20878 = true := by
 decide +kernel
def pointBounds20878 : List (Nat × Nat × Nat) := [(2740532224,100577385382146,100577766076900)]
theorem point_links_checked20878 : (cuts20878.take 1).map (fun c => (2740453377-1+2*2^9*c.k,100577012032797+c.lower,100577392727335+c.upper)) = pointBounds20878 := by
 decide +kernel
def cuts20879 : List PrefixCut := [⟨33,163712607,163712699⟩,
⟨117,571752775,571753102⟩,
⟨128,627108856,627109214⟩]
theorem checked20879 : checkPrefixCuts (2^48) 2740584449 9 Manual.Count131072.C020879.packed 128 cuts20879 = true := by
 decide +kernel
def pointBounds20879 : List (Nat × Nat × Nat) := [(2740618240,100577794051295,100578174746283),(2740704256,100578202091463,100578582786686)]
theorem point_links_checked20879 : (cuts20879.take 2).map (fun c => (2740584449-1+2*2^9*c.k,100577630338688+c.lower,100578011033584+c.upper)) = pointBounds20879 := by
 decide +kernel
def cuts20880 : List PrefixCut := [⟨73,354827996,354828201⟩,
⟨128,624614012,624614377⟩]
theorem checked20880 : checkPrefixCuts (2^48) 2740715521 9 Manual.Count131072.C020880.packed 128 cuts20880 = true := by
 decide +kernel
def pointBounds20880 : List (Nat × Nat × Nat) := [(2740790272,100578612275540,100578992970999)]
theorem point_links_checked20880 : (cuts20880.take 1).map (fun c => (2740715521-1+2*2^9*c.k,100578257447544+c.lower,100578638142798+c.upper)) = pointBounds20880 := by
 decide +kernel
def cuts20881 : List PrefixCut := [⟨29,134531470,134531549⟩,
⟨113,539452360,539452672⟩,
⟨128,613390392,613390744⟩]
theorem checked20881 : checkPrefixCuts (2^48) 2740846593 9 Manual.Count131072.C020881.packed 128 cuts20881 = true := by
 decide +kernel
def pointBounds20881 : List (Nat × Nat × Nat) := [(2740876288,100579016593026,100579397288724),(2740962304,100579421513916,100579802209847)]
theorem point_links_checked20881 : (cuts20881.take 2).map (fun c => (2740846593-1+2*2^9*c.k,100578882061556+c.lower,100579262757175+c.upper)) = pointBounds20881 := by
 decide +kernel
def cuts20882 : List PrefixCut := [⟨69,334461695,334461888⟩,
⟨128,618187693,618188045⟩]
theorem checked20882 : checkPrefixCuts (2^48) 2740977665 9 Manual.Count131072.C020882.packed 128 cuts20882 = true := by
 decide +kernel
def pointBounds20882 : List (Nat × Nat × Nat) := [(2741048320,100579829913643,100580210609807)]
theorem point_links_checked20882 : (cuts20882.take 1).map (fun c => (2740977665-1+2*2^9*c.k,100579495451948+c.lower,100579876147919+c.upper)) = pointBounds20882 := by
 decide +kernel
def cuts20883 : List PrefixCut := [⟨25,121477570,121477640⟩,
⟨109,529235456,529235767⟩,
⟨128,623497498,623497862⟩]
theorem checked20883 : checkPrefixCuts (2^48) 2741108737 9 Manual.Count131072.C020883.packed 128 cuts20883 = true := by
 decide +kernel
def pointBounds20883 : List (Nat × Nat × Nat) := [(2741134336,100580235117211,100580615813604),(2741220352,100580642875097,100581023571731)]
theorem point_links_checked20883 : (cuts20883.take 2).map (fun c => (2741108737-1+2*2^9*c.k,100580113639641+c.lower,100580494335964+c.upper)) = pointBounds20883 := by
 decide +kernel
def cuts20884 : List PrefixCut := [⟨65,315639452,315639631⟩,
⟨128,626137364,626137716⟩]
theorem checked20884 : checkPrefixCuts (2^48) 2741239809 9 Manual.Count131072.C020884.packed 128 cuts20884 = true := by
 decide +kernel
def pointBounds20884 : List (Nat × Nat × Nat) := [(2741306368,100581052776591,100581433473457)]
theorem point_links_checked20884 : (cuts20884.take 1).map (fun c => (2741239809-1+2*2^9*c.k,100580737137139+c.lower,100581117833826+c.upper)) = pointBounds20884 := by
 decide +kernel
def cuts20885 : List PrefixCut := [⟨21,100725436,100725496⟩,
⟨105,511935914,511936220⟩,
⟨128,623129947,623130315⟩]
theorem checked20885 : checkPrefixCuts (2^48) 2741370881 9 Manual.Count131072.C020885.packed 128 cuts20885 = true := by
 decide +kernel
def pointBounds20885 : List (Nat × Nat × Nat) := [(2741392384,100581463999939,100581844697038),(2741478400,100581875210417,100582255907762)]
theorem point_links_checked20885 : (cuts20885.take 2).map (fun c => (2741370881-1+2*2^9*c.k,100581363274503+c.lower,100581743971542+c.upper)) = pointBounds20885 := by
 decide +kernel
def cuts20886 : List PrefixCut := [⟨61,300414204,300414375⟩,
⟨128,624332232,624332593⟩]
theorem checked20886 : checkPrefixCuts (2^48) 2741501953 9 Manual.Count131072.C020886.packed 128 cuts20886 = true := by
 decide +kernel
def pointBounds20886 : List (Nat × Nat × Nat) := [(2741564416,100582286818654,100582667516232)]
theorem point_links_checked20886 : (cuts20886.take 1).map (fun c => (2741501953-1+2*2^9*c.k,100581986404450+c.lower,100582367101857+c.upper)) = pointBounds20886 := by
 decide +kernel
def cuts20887 : List PrefixCut := [⟨17,80695906,80695952⟩,
⟨101,483962461,483962743⟩,
⟨128,613214529,613214887⟩]
theorem checked20887 : checkPrefixCuts (2^48) 2741633025 9 Manual.Count131072.C020887.packed 128 cuts20887 = true := by
 decide +kernel
def pointBounds20887 : List (Nat × Nat × Nat) := [(2741650432,100582691432588,100583072130402),(2741736448,100583094699143,100583475397193)]
theorem point_links_checked20887 : (cuts20887.take 2).map (fun c => (2741633025-1+2*2^9*c.k,100582610736682+c.lower,100582991434450+c.upper)) = pointBounds20887 := by
 decide +kernel
def cuts20888 : List PrefixCut := [⟨57,273796538,273796695⟩,
⟨128,624067064,624067426⟩]
theorem checked20888 : checkPrefixCuts (2^48) 2741764097 9 Manual.Count131072.C020888.packed 128 cuts20888 = true := by
 decide +kernel
def pointBounds20888 : List (Nat × Nat × Nat) := [(2741822464,100583497747749,100583878446032)]
theorem point_links_checked20888 : (cuts20888.take 1).map (fun c => (2741764097-1+2*2^9*c.k,100583223951211+c.lower,100583604649337+c.upper)) = pointBounds20888 := by
 decide +kernel
def cuts20889 : List PrefixCut := [⟨13,62518002,62518038⟩,
⟨97,458868799,458869067⟩,
⟨128,608433864,608434222⟩]
theorem checked20889 : checkPrefixCuts (2^48) 2741895169 9 Manual.Count131072.C020889.packed 128 cuts20889 = true := by
 decide +kernel
def pointBounds20889 : List (Nat × Nat × Nat) := [(2741908480,100583910536277,100584291234801),(2741994496,100584306887074,100584687585830)]
theorem point_links_checked20889 : (cuts20889.take 2).map (fun c => (2741895169-1+2*2^9*c.k,100583848018275+c.lower,100584228716763+c.upper)) = pointBounds20889 := by
 decide +kernel
def cuts20890 : List PrefixCut := [⟨53,257346403,257346551⟩,
⟨128,611484321,611484675⟩]
theorem checked20890 : checkPrefixCuts (2^48) 2742026241 9 Manual.Count131072.C020890.packed 128 cuts20890 = true := by
 decide +kernel
def pointBounds20890 : List (Nat × Nat × Nat) := [(2742080512,100584713798542,100585094497536)]
theorem point_links_checked20890 : (cuts20890.take 1).map (fun c => (2742026241-1+2*2^9*c.k,100584456452139+c.lower,100584837150985+c.upper)) = pointBounds20890 := by
 decide +kernel
def cuts20891 : List PrefixCut := [⟨9,44959422,44959445⟩,
⟨93,454206163,454206424⟩,
⟨128,623669755,623670113⟩]
theorem checked20891 : checkPrefixCuts (2^48) 2742157313 9 Manual.Count131072.C020891.packed 128 cuts20891 = true := by
 decide +kernel
def pointBounds20891 : List (Nat × Nat × Nat) := [(2742166528,100585112895882,100585493595105),(2742252544,100585522142623,100585902842084)]
theorem point_links_checked20891 : (cuts20891.take 2).map (fun c => (2742157313-1+2*2^9*c.k,100585067936460+c.lower,100585448635660+c.upper)) = pointBounds20891 := by
 decide +kernel
def cuts20892 : List PrefixCut := [⟨49,235972583,235972721⟩,
⟨128,621689729,621690093⟩]
theorem checked20892 : checkPrefixCuts (2^48) 2742288385 9 Manual.Count131072.C020892.packed 128 cuts20892 = true := by
 decide +kernel
def pointBounds20892 : List (Nat × Nat × Nat) := [(2742338560,100585927578798,100586308278494)]
theorem point_links_checked20892 : (cuts20892.take 1).map (fun c => (2742288385-1+2*2^9*c.k,100585691606215+c.lower,100586072305773+c.upper)) = pointBounds20892 := by
 decide +kernel
def cuts20893 : List PrefixCut := [⟨5,24632961,24632975⟩,
⟨89,422859221,422859462⟩,
⟨128,608420171,608420521⟩]
theorem checked20893 : checkPrefixCuts (2^48) 2742419457 9 Manual.Count131072.C020893.packed 128 cuts20893 = true := by
 decide +kernel
def pointBounds20893 : List (Nat × Nat × Nat) := [(2742424576,100586337928905,100586718628841),(2742510592,100586736155165,100587116855328)]
theorem point_links_checked20893 : (cuts20893.take 2).map (fun c => (2742419457-1+2*2^9*c.k,100586313295944+c.lower,100586693995866+c.upper)) = pointBounds20893 := by
 decide +kernel
def cuts20894 : List PrefixCut := [⟨45,218194950,218195077⟩,
⟨128,612188531,612188897⟩]
theorem checked20894 : checkPrefixCuts (2^48) 2742550529 9 Manual.Count131072.C020894.packed 128 cuts20894 = true := by
 decide +kernel
def pointBounds20894 : List (Nat × Nat × Nat) := [(2742596608,100587139911065,100587520611464)]
theorem point_links_checked20894 : (cuts20894.take 1).map (fun c => (2742550529-1+2*2^9*c.k,100586921716115+c.lower,100587302416387+c.upper)) = pointBounds20894 := by
 decide +kernel
def cuts20895 : List PrefixCut := [⟨1,5336635,5336638⟩,
⟨85,412556561,412556799⟩,
⟨128,619240360,619240714⟩]
theorem checked20895 : checkPrefixCuts (2^48) 2742681601 9 Manual.Count131072.C020895.packed 128 cuts20895 = true := by
 decide +kernel
def pointBounds20895 : List (Nat × Nat × Nat) := [(2742682624,100587539241281,100587919941922),(2742768640,100587946461207,100588327162083)]
theorem point_links_checked20895 : (cuts20895.take 2).map (fun c => (2742681601-1+2*2^9*c.k,100587533904646+c.lower,100587914605284+c.upper)) = pointBounds20895 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000027
