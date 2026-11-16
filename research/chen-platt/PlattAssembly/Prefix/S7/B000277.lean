import PlattAssemblyKernel
import PlattCertificates.Count131072.C068864
import PlattCertificates.Count131072.C068865
import PlattCertificates.Count131072.C068866
import PlattCertificates.Count131072.C068867
import PlattCertificates.Count131072.C068868
import PlattCertificates.Count131072.C068869
import PlattCertificates.Count131072.C068870
import PlattCertificates.Count131072.C068871
import PlattCertificates.Count131072.C068872
import PlattCertificates.Count131072.C068873
import PlattCertificates.Count131072.C068874
import PlattCertificates.Count131072.C068875
import PlattCertificates.Count131072.C068876
import PlattCertificates.Count131072.C068877
import PlattCertificates.Count131072.C068878
import PlattCertificates.Count131072.C068879
import PlattCertificates.Count131072.C068880
import PlattCertificates.Count131072.C068881
import PlattCertificates.Count131072.C068882
import PlattCertificates.Count131072.C068883
import PlattCertificates.Count131072.C068884
import PlattCertificates.Count131072.C068885
import PlattCertificates.Count131072.C068886
import PlattCertificates.Count131072.C068887
import PlattCertificates.Count131072.C068888
import PlattCertificates.Count131072.C068889
import PlattCertificates.Count131072.C068890
import PlattCertificates.Count131072.C068891
import PlattCertificates.Count131072.C068892
import PlattCertificates.Count131072.C068893
import PlattCertificates.Count131072.C068894
import PlattCertificates.Count131072.C068895
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000277
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts68864 : List PrefixCut := [⟨51,141171858,141171944⟩,
⟨64,178171149,178171255⟩]
theorem checked68864 : checkPrefixCuts (2^48) 9030074369 10 Manual.Count131072.C068864.packed 64 cuts68864 = true := by
 decide +kernel
def pointBounds68864 : List (Nat × Nat × Nat) := [(9030178816,115613172562632,115613561949936)]
theorem point_links_checked68864 : (cuts68864.take 1).map (fun c => (9030074369-1+2*2^10*c.k,115613031390774+c.lower,115613420777992+c.upper)) = pointBounds68864 := by
 decide +kernel
def cuts68865 : List PrefixCut := [⟨64,175799648,175799747⟩]
theorem checked68865 : checkPrefixCuts (2^48) 9030205441 10 Manual.Count131072.C068865.packed 64 cuts68865 = true := by
 decide +kernel
def cuts68866 : List PrefixCut := [⟨61,166882614,166882717⟩,
⟨64,175360712,175360821⟩]
theorem checked68866 : checkPrefixCuts (2^48) 9030336513 10 Manual.Count131072.C068866.packed 64 cuts68866 = true := by
 decide +kernel
def pointBounds68866 : List (Nat × Nat × Nat) := [(9030461440,115613552244185,115613941631711)]
theorem point_links_checked68866 : (cuts68866.take 1).map (fun c => (9030336513-1+2*2^10*c.k,115613385361571+c.lower,115613774748994+c.upper)) = pointBounds68866 := by
 decide +kernel
def cuts68867 : List PrefixCut := [⟨64,175576355,175576462⟩]
theorem checked68867 : checkPrefixCuts (2^48) 9030467585 10 Manual.Count131072.C068867.packed 64 cuts68867 = true := by
 decide +kernel
def cuts68868 : List PrefixCut := [⟨64,175947822,175947926⟩]
theorem checked68868 : checkPrefixCuts (2^48) 9030598657 10 Manual.Count131072.C068868.packed 64 cuts68868 = true := by
 decide +kernel
def cuts68869 : List PrefixCut := [⟨7,19355664,19355677⟩,
⟨64,177285512,177285619⟩]
theorem checked68869 : checkPrefixCuts (2^48) 9030729729 10 Manual.Count131072.C068869.packed 64 cuts68869 = true := by
 decide +kernel
def pointBounds68869 : List (Nat × Nat × Nat) := [(9030744064,115613931602124,115614320989880)]
theorem point_links_checked68869 : (cuts68869.take 1).map (fun c => (9030729729-1+2*2^10*c.k,115613912246460+c.lower,115614301634203+c.upper)) = pointBounds68869 := by
 decide +kernel
def cuts68870 : List PrefixCut := [⟨64,180617908,180618013⟩]
theorem checked68870 : checkPrefixCuts (2^48) 9030860801 10 Manual.Count131072.C068870.packed 64 cuts68870 = true := by
 decide +kernel
def cuts68871 : List PrefixCut := [⟨17,47873435,47873461⟩,
⟨64,176407686,176407792⟩]
theorem checked68871 : checkPrefixCuts (2^48) 9030991873 10 Manual.Count131072.C068871.packed 64 cuts68871 = true := by
 decide +kernel
def pointBounds68871 : List (Nat × Nat × Nat) := [(9031026688,115614318023315,115614707411296)]
theorem point_links_checked68871 : (cuts68871.take 1).map (fun c => (9030991873-1+2*2^10*c.k,115614270149880+c.lower,115614659537835+c.upper)) = pointBounds68871 := by
 decide +kernel
def cuts68872 : List PrefixCut := [⟨64,178991982,178992088⟩]
theorem checked68872 : checkPrefixCuts (2^48) 9031122945 10 Manual.Count131072.C068872.packed 64 cuts68872 = true := by
 decide +kernel
def cuts68873 : List PrefixCut := [⟨27,75766152,75766196⟩,
⟨64,179425715,179425818⟩]
theorem checked68873 : checkPrefixCuts (2^48) 9031254017 10 Manual.Count131072.C068873.packed 64 cuts68873 = true := by
 decide +kernel
def pointBounds68873 : List (Nat × Nat × Nat) := [(9031309312,115614701315700,115615090703911)]
theorem point_links_checked68873 : (cuts68873.take 1).map (fun c => (9031254017-1+2*2^10*c.k,115614625549548+c.lower,115615014937715+c.upper)) = pointBounds68873 := by
 decide +kernel
def cuts68874 : List PrefixCut := [⟨64,177740153,177740250⟩]
theorem checked68874 : checkPrefixCuts (2^48) 9031385089 10 Manual.Count131072.C068874.packed 64 cuts68874 = true := by
 decide +kernel
def cuts68875 : List PrefixCut := [⟨37,103127374,103127431⟩,
⟨64,177488247,177488347⟩]
theorem checked68875 : checkPrefixCuts (2^48) 9031516161 10 Manual.Count131072.C068875.packed 64 cuts68875 = true := by
 decide +kernel
def pointBounds68875 : List (Nat × Nat × Nat) := [(9031591936,115615085842790,115615475231214)]
theorem point_links_checked68875 : (cuts68875.take 1).map (fun c => (9031516161-1+2*2^10*c.k,115614982715416+c.lower,115615372103783+c.upper)) = pointBounds68875 := by
 decide +kernel
def cuts68876 : List PrefixCut := [⟨64,180757998,180758105⟩]
theorem checked68876 : checkPrefixCuts (2^48) 9031647233 10 Manual.Count131072.C068876.packed 64 cuts68876 = true := by
 decide +kernel
def cuts68877 : List PrefixCut := [⟨47,130705091,130705168⟩,
⟨64,178324530,178324636⟩]
theorem checked68877 : checkPrefixCuts (2^48) 9031778305 10 Manual.Count131072.C068877.packed 64 cuts68877 = true := by
 decide +kernel
def pointBounds68877 : List (Nat × Nat × Nat) := [(9031874560,115615471666752,115615861055403)]
theorem point_links_checked68877 : (cuts68877.take 1).map (fun c => (9031778305-1+2*2^10*c.k,115615340961661+c.lower,115615730350235+c.upper)) = pointBounds68877 := by
 decide +kernel
def cuts68878 : List PrefixCut := [⟨64,177823321,177823430⟩]
theorem checked68878 : checkPrefixCuts (2^48) 9031909377 10 Manual.Count131072.C068878.packed 64 cuts68878 = true := by
 decide +kernel
def cuts68879 : List PrefixCut := [⟨57,159247227,159247323⟩,
⟨64,177883069,177883176⟩]
theorem checked68879 : checkPrefixCuts (2^48) 9032040449 10 Manual.Count131072.C068879.packed 64 cuts68879 = true := by
 decide +kernel
def pointBounds68879 : List (Nat × Nat × Nat) := [(9032157184,115615856356739,115616245745624)]
theorem point_links_checked68879 : (cuts68879.take 1).map (fun c => (9032040449-1+2*2^10*c.k,115615697109512+c.lower,115616086498301+c.upper)) = pointBounds68879 := by
 decide +kernel
def cuts68880 : List PrefixCut := [⟨64,175917197,175917301⟩]
theorem checked68880 : checkPrefixCuts (2^48) 9032171521 10 Manual.Count131072.C068880.packed 64 cuts68880 = true := by
 decide +kernel
def cuts68881 : List PrefixCut := [⟨64,176288602,176288703⟩]
theorem checked68881 : checkPrefixCuts (2^48) 9032302593 10 Manual.Count131072.C068881.packed 64 cuts68881 = true := by
 decide +kernel
def cuts68882 : List PrefixCut := [⟨3,8102295,8102300⟩,
⟨64,178311602,178311706⟩]
theorem checked68882 : checkPrefixCuts (2^48) 9032433665 10 Manual.Count131072.C068882.packed 64 cuts68882 = true := by
 decide +kernel
def pointBounds68882 : List (Nat × Nat × Nat) := [(9032439808,115616235300675,115616624689781)]
theorem point_links_checked68882 : (cuts68882.take 1).map (fun c => (9032433665-1+2*2^10*c.k,115616227198380+c.lower,115616616587481+c.upper)) = pointBounds68882 := by
 decide +kernel
def cuts68883 : List PrefixCut := [⟨64,177436472,177436576⟩]
theorem checked68883 : checkPrefixCuts (2^48) 9032564737 10 Manual.Count131072.C068883.packed 64 cuts68883 = true := by
 decide +kernel
def cuts68884 : List PrefixCut := [⟨13,36272261,36272281⟩,
⟨64,179677522,179677622⟩]
theorem checked68884 : checkPrefixCuts (2^48) 9032695809 10 Manual.Count131072.C068884.packed 64 cuts68884 = true := by
 decide +kernel
def pointBounds68884 : List (Nat × Nat × Nat) := [(9032722432,115616619218715,115617008608044)]
theorem point_links_checked68884 : (cuts68884.take 1).map (fun c => (9032695809-1+2*2^10*c.k,115616582946454+c.lower,115616972335763+c.upper)) = pointBounds68884 := by
 decide +kernel
def cuts68885 : List PrefixCut := [⟨64,178958211,178958315⟩]
theorem checked68885 : checkPrefixCuts (2^48) 9032826881 10 Manual.Count131072.C068885.packed 64 cuts68885 = true := by
 decide +kernel
def cuts68886 : List PrefixCut := [⟨23,63630343,63630378⟩,
⟨64,175465628,175465729⟩]
theorem checked68886 : checkPrefixCuts (2^48) 9032957953 10 Manual.Count131072.C068886.packed 64 cuts68886 = true := by
 decide +kernel
def pointBounds68886 : List (Nat × Nat × Nat) := [(9033005056,115617005212530,115617394602078)]
theorem point_links_checked68886 : (cuts68886.take 1).map (fun c => (9032957953-1+2*2^10*c.k,115616941582187+c.lower,115617330971700+c.upper)) = pointBounds68886 := by
 decide +kernel
def cuts68887 : List PrefixCut := [⟨64,176989926,176990028⟩]
theorem checked68887 : checkPrefixCuts (2^48) 9033089025 10 Manual.Count131072.C068887.packed 64 cuts68887 = true := by
 decide +kernel
def cuts68888 : List PrefixCut := [⟨33,90955623,90955674⟩,
⟨64,177298958,177299062⟩]
theorem checked68888 : checkPrefixCuts (2^48) 9033220097 10 Manual.Count131072.C068888.packed 64 cuts68888 = true := by
 decide +kernel
def pointBounds68888 : List (Nat × Nat × Nat) := [(9033287680,115617384993364,115617774383131)]
theorem point_links_checked68888 : (cuts68888.take 1).map (fun c => (9033220097-1+2*2^10*c.k,115617294037741+c.lower,115617683427457+c.upper)) = pointBounds68888 := by
 decide +kernel
def cuts68889 : List PrefixCut := [⟨64,178386965,178387073⟩]
theorem checked68889 : checkPrefixCuts (2^48) 9033351169 10 Manual.Count131072.C068889.packed 64 cuts68889 = true := by
 decide +kernel
def cuts68890 : List PrefixCut := [⟨43,118777795,118777867⟩,
⟨64,176140946,176141049⟩]
theorem checked68890 : checkPrefixCuts (2^48) 9033482241 10 Manual.Count131072.C068890.packed 64 cuts68890 = true := by
 decide +kernel
def pointBounds68890 : List (Nat × Nat × Nat) := [(9033570304,115617768501459,115618157891459)]
theorem point_links_checked68890 : (cuts68890.take 1).map (fun c => (9033482241-1+2*2^10*c.k,115617649723664+c.lower,115618039113592+c.upper)) = pointBounds68890 := by
 decide +kernel
def cuts68891 : List PrefixCut := [⟨64,177509349,177509457⟩]
theorem checked68891 : checkPrefixCuts (2^48) 9033613313 10 Manual.Count131072.C068891.packed 64 cuts68891 = true := by
 decide +kernel
def cuts68892 : List PrefixCut := [⟨53,148935135,148935222⟩,
⟨64,179656678,179656781⟩]
theorem checked68892 : checkPrefixCuts (2^48) 9033744385 10 Manual.Count131072.C068892.packed 64 cuts68892 = true := by
 decide +kernel
def pointBounds68892 : List (Nat × Nat × Nat) := [(9033852928,115618152309094,115618541699320)]
theorem point_links_checked68892 : (cuts68892.take 1).map (fun c => (9033744385-1+2*2^10*c.k,115618003373959+c.lower,115618392764098+c.upper)) = pointBounds68892 := by
 decide +kernel
def cuts68893 : List PrefixCut := [⟨64,177223791,177223892⟩]
theorem checked68893 : checkPrefixCuts (2^48) 9033875457 10 Manual.Count131072.C068893.packed 64 cuts68893 = true := by
 decide +kernel
def cuts68894 : List PrefixCut := [⟨63,174074381,174074484⟩,
⟨64,176753867,176753971⟩]
theorem checked68894 : checkPrefixCuts (2^48) 9034006529 10 Manual.Count131072.C068894.packed 64 cuts68894 = true := by
 decide +kernel
def pointBounds68894 : List (Nat × Nat × Nat) := [(9034135552,115618534328809,115618923719255)]
theorem point_links_checked68894 : (cuts68894.take 1).map (fun c => (9034006529-1+2*2^10*c.k,115618360254428+c.lower,115618749644771+c.upper)) = pointBounds68894 := by
 decide +kernel
def cuts68895 : List PrefixCut := [⟨64,179555380,179555477⟩]
theorem checked68895 : checkPrefixCuts (2^48) 9034137601 10 Manual.Count131072.C068895.packed 64 cuts68895 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000277
