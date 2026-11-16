import PlattPointSubsetKernel
import PlattPointPackets.S8B000126
import PlattPointPackets.S8B000127
import PlattPointPackets.S8B000128
import PlattPointPackets.S8B000129
import PlattPointPackets.S8B000130
import PlattPointPackets.S8B000131
import PlattPointPackets.S8B000132
import PlattPointPackets.S8B000133
import PlattPointPackets.S8B000134
import PlattPointPackets.S8B000135
import PlattPointPackets.S8B000136
import PlattPointPackets.S8B000137
import PlattPointPackets.S8B000138
import PlattPointPackets.S8B000139
import PlattPointPackets.S8B000140
import PlattPointPackets.S8B000141
import PlattPointPackets.S8B000142
import PlattPointPackets.S8B000143
import PlattPointPackets.S8B000144
import PlattPointPackets.S8B000145
import PlattGlobalGrid.S8B000113
namespace ChenEffective.PlattWindow.PointCovers.S8B000113
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((((((((((((((((((ChenEffective.PlattWindow.PointPackets.S8B000126.points ++ ChenEffective.PlattWindow.PointPackets.S8B000127.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000128.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000129.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000130.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000131.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000132.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000133.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000134.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000135.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000136.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000137.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000138.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000139.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000140.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000141.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000142.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000143.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000144.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000145.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S8B000113.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S8B000113.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S8B000113
