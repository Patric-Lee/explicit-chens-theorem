import PlattPointSubsetKernel
import PlattPointPackets.S5B000133
import PlattPointPackets.S5B000134
import PlattPointPackets.S5B000135
import PlattPointPackets.S5B000136
import PlattPointPackets.S5B000137
import PlattPointPackets.S5B000138
import PlattPointPackets.S5B000139
import PlattPointPackets.S5B000140
import PlattPointPackets.S5B000141
import PlattPointPackets.S5B000142
import PlattPointPackets.S5B000143
import PlattPointPackets.S5B000144
import PlattGlobalGrid.S8B000049
namespace ChenEffective.PlattWindow.PointCovers.S8B000049
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((((((((((ChenEffective.PlattWindow.PointPackets.S5B000133.points ++ ChenEffective.PlattWindow.PointPackets.S5B000134.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000135.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000136.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000137.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000138.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000139.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000140.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000141.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000142.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000143.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000144.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S8B000049.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S8B000049.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S8B000049
