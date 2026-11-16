import PlattPointSubsetKernel
import PlattPointPackets.S6B000129
import PlattPointPackets.S6B000130
import PlattPointPackets.S6B000131
import PlattPointPackets.S6B000132
import PlattPointPackets.S6B000133
import PlattPointPackets.S6B000134
import PlattPointPackets.S6B000135
import PlattPointPackets.S6B000136
import PlattPointPackets.S6B000137
import PlattPointPackets.S6B000138
import PlattPointPackets.S6B000139
import PlattPointPackets.S6B000140
import PlattPointPackets.S6B000141
import PlattPointPackets.S6B000142
import PlattGlobalGrid.S8B000074
namespace ChenEffective.PlattWindow.PointCovers.S8B000074
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((((((((((((ChenEffective.PlattWindow.PointPackets.S6B000129.points ++ ChenEffective.PlattWindow.PointPackets.S6B000130.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000131.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000132.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000133.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000134.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000135.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000136.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000137.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000138.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000139.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000140.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000141.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000142.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S8B000074.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S8B000074.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S8B000074
