import PlattPointSubsetKernel
import PlattPointPackets.S4B000131
import PlattPointPackets.S4B000132
import PlattPointPackets.S4B000133
import PlattPointPackets.S4B000134
import PlattPointPackets.S4B000135
import PlattPointPackets.S4B000136
import PlattPointPackets.S4B000137
import PlattPointPackets.S4B000138
import PlattPointPackets.S4B000139
import PlattPointPackets.S4B000140
import PlattGlobalGrid.S8B000017
namespace ChenEffective.PlattWindow.PointCovers.S8B000017
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((((((((ChenEffective.PlattWindow.PointPackets.S4B000131.points ++ ChenEffective.PlattWindow.PointPackets.S4B000132.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000133.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000134.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000135.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000136.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000137.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000138.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000139.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000140.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S8B000017.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S8B000017.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S8B000017
